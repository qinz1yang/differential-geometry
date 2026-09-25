import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Convergence.Exhaustion
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.Compactness.MetricExtension
import DifferentialGeometry.Geometry.Metric.Convergence.Restriction
import DifferentialGeometry.Topology.Manifold.OpenEmbedding
import DifferentialGeometry.Topology.Manifold.OpenSubtypeDiffeomorph

noncomputable section
open Set Filter
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.CheegerGromovCompactness

universe u uE uH
variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  {H : Type uH} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
attribute [local instance] PointedRiemannianManifold.topology PointedRiemannianManifold.charted
  PointedRiemannianManifold.smooth PointedRiemannianManifold.t2
  PointedRiemannianManifold.sigmaCompact PointedRiemannianManifold.t2TangentBundle

theorem exists_pointed_maps_of_injective_local_diffeomorphs
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    [PreconnectedSpace P.M] (f : ℕ → ℕ) (U : ℕ → TopologicalSpace.Opens P.M)
    (hp : ∀ i, P.basepoint ∈ U i)
    (psi : ∀ i, U i → (X.obj (f i)).M)
    (hpsi : ∀ i, IsLocalDiffeomorph I I ∞ (psi i)) (hinj : ∀ i, Function.Injective (psi i))
    (hbase : ∀ i, psi i ⟨P.basepoint, hp i⟩ = (X.obj (f i)).basepoint)
    (hexhaust : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ F : PointedRiemannianConvergenceMaps X P (f ∘ k),
      (∀ i (x : U (k i)), F.map i x = psi (k i) x) ∧
      (∀ i, F.source i ⊆ U (k i)) ∧
      (∀ i, IsCompact (closure (F.source i))) ∧ (∀ i, IsConnected (F.source i)) ∧
      ∀ i, F.target i = F.map i '' F.source i := by
  let _ : Nonempty P.M := ⟨P.basepoint⟩
  let e (i) := DifferentialGeometry.Topology.Manifold.diffeomorphOntoImage (psi i) (hpsi i) (hinj i)
  let iU (i) := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I (U i) ⟨⟨P.basepoint, hp i⟩⟩
  let iV (i) := DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph I (hpsi i).image
    ⟨e i ⟨P.basepoint, hp i⟩⟩
  let Phi (i) := ((iU i).symm.trans (e i).toPartialDiffeomorph).trans (iV i)
  have hsrc (i) : (Phi i).source = U i := by
    ext x
    change (x ∈ (iU i).target ∧ (iU i).symm x ∈ (univ : Set (U i))) ∧
      (e i ((iU i).symm x)) ∈ (univ : Set (hpsi i).image) ↔ x ∈ U i
    simp only [iU, DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_target, mem_univ, and_true]
    rfl
  have hmap (i) (x : U i) : Phi i x = psi i x := by
    change psi i ((iU i).symm x) = psi i x
    rw [DifferentialGeometry.Manifold.openSubtypePartialDiffeomorph_symm_apply I (U i)
      ⟨⟨P.basepoint, hp i⟩⟩ x.property]
  have hpmap (i) : Phi i P.basepoint = (X.obj (f i)).basepoint :=
    (hmap i ⟨P.basepoint, hp i⟩).trans (hbase i)
  obtain ⟨k, hk, F, hF, _, hFsource, hcompact, hconn⟩ :=
    PointedRiemannianConvergenceMaps.exists_subsequence_restriction_of_eventually_contains_compacts Phi hpmap
      (fun K hK => by simpa only [hsrc] using hexhaust K hK)
  refine ⟨k, hk, F, ?_, ?_, hcompact, hconn, ?_⟩
  · intro i x
    rw [hF]
    exact hmap (k i) x
  · intro i
    simpa only [hsrc] using hFsource i
  · intro i
    exact (F.partialDiffeomorph i).image_source_eq_target.symm

theorem exists_pointed_convergence_of_injective_local_diffeomorphs
    {X : PointedRiemannianSeq.{u, uE, uH} I} {P : PointedRiemannianManifold.{u, uE, uH} I}
    [PreconnectedSpace P.M] (f : ℕ → ℕ) (U : ℕ → TopologicalSpace.Opens P.M)
    (hp : ∀ i, P.basepoint ∈ U i)
    (psi : ∀ i, U i → (X.obj (f i)).M)
    (hpsi : ∀ i, IsLocalDiffeomorph I I ∞ (psi i)) (hinj : ∀ i, Function.Injective (psi i))
    (hbase : ∀ i, psi i ⟨P.basepoint, hp i⟩ = (X.obj (f i)).basepoint)
    (hexhaust : ∀ K : Set P.M, IsCompact K → ∀ᶠ i in atTop, K ⊆ U i)
    (hlocal : ∀ K : Set P.M, IsCompact K →
      ∃ V : TopologicalSpace.Opens P.M, K ⊆ V ∧
        ∃ G : ℕ → SmoothRiemannianMetric I V,
          MetricCInfConvergenceOnCompacts G (P.metric.restrictOpen V) (P.metric.restrictOpen V) ∧
          ∀ᶠ i in atTop, ∃ hVU : V ≤ U i,
            ∀ (x : V) (v w : TangentSpace I x),
              (G i).inner x v w = (X.obj (f i)).metric.inner
                (psi i (TopologicalSpace.Opens.inclusion hVU x))
                (mfderiv I I (fun y : V => psi i (TopologicalSpace.Opens.inclusion hVU y)) x v)
                (mfderiv I I (fun y : V => psi i (TopologicalSpace.Opens.inclusion hVU y)) x w)) :
    ∃ k : ℕ → ℕ, StrictMono k ∧ ∃ F : PointedRiemannianConvergenceMaps X P (f ∘ k),
      (∀ i (x : U (k i)), F.map i x = psi (k i) x) ∧
      (∀ i, F.source i ⊆ U (k i)) ∧
      (∀ i, IsCompact (closure (F.source i))) ∧ (∀ i, IsConnected (F.source i)) ∧
      ∃ C : MetricConvergenceData F,
        ∀ i, C.domain i = CanonicalMetricCompactness.canonicalSourceData F i := by
  let _ : CompleteSpace E := FiniteDimensional.complete ℝ E
  let _ : LocallyCompactSpace P.M := Manifold.locallyCompact_of_finiteDimensional I
  obtain ⟨k, hk, F, hmap, hsource, hcpt, hconn, _⟩ :=
    exists_pointed_maps_of_injective_local_diffeomorphs f U hp psi hpsi hinj hbase hexhaust
  refine ⟨k, hk, F, hmap, hsource, hcpt, hconn, ?_⟩
  apply exists_canonicalMetricConvergenceData_of_local_pullback F
  intro K hK
  obtain ⟨V, hKV, G, hconv, hG⟩ := hlocal K hK
  obtain ⟨W0, hW0, hKW, hWV, hWcompact⟩ :=
    exists_open_between_and_isCompact_closure hK V.isOpen hKV
  let W : TopologicalSpace.Opens P.M := ⟨W0, hW0⟩
  have hWV' : W ≤ V := subset_closure.trans hWV
  let _ : SigmaCompactSpace V := isSigmaCompact_iff_sigmaCompactSpace.mp
    (Geometry.isSigmaCompact_of_isOpen I V.isOpen)
  let GW := fun n => (G (k n)).restrictOpenOfSubset hWV'
  have hlimit : (P.metric.restrictOpen V).restrictOpenOfSubset hWV' = P.metric.restrictOpen W := by
    apply SmoothRiemannianMetric.ext_inner
    intro x v w
    rfl
  refine ⟨W, hKW, GW, ?_, ?_⟩
  · have hh := (hconv.comp_subseq hk).restrictOpenOfSubset hWV'
    rwa [hlimit] at hh
  obtain ⟨N, hN⟩ := F.source_subset hWcompact
  filter_upwards [hk.tendsto_atTop.eventually hG, eventually_ge_atTop N] with n hn hnN
  obtain ⟨hVU, hGn⟩ := hn
  have hWsource : (W : Set P.M) ⊆ F.source n := subset_closure.trans (hN n hnN)
  refine ⟨hWsource, ?_⟩
  intro x v w
  have hmaps : (fun y : V => psi (k n) (TopologicalSpace.Opens.inclusion hVU y)) =
      fun y : V => F.map n y := by
    funext y
    exact (hmap n (TopologicalSpace.Opens.inclusion hVU y)).symm
  have hd (z : TangentSpace I x) :
      mfderiv I I (fun y : V => F.map n y) (TopologicalSpace.Opens.inclusion hWV' x) z =
        mfderiv I I (F.map n) (x : P.M) z := by
    exact congrArg (fun A => A z) (DifferentialGeometry.mfderiv_restrict_open (I := I) (J := I) (F.map n) V
      (TopologicalSpace.Opens.inclusion hWV' x))
  change (G (k n)).inner (TopologicalSpace.Opens.inclusion hWV' x) v w = _
  have hh := hGn (TopologicalSpace.Opens.inclusion hWV' x) v w
  rw [hmaps] at hh
  have hpval := hmap n (TopologicalSpace.Opens.inclusion hVU (TopologicalSpace.Opens.inclusion hWV' x))
  exact hh.trans (by
    rw [← hpval]
    exact congrArg₂ (fun v' w' => (X.obj (f (k n))).metric.inner (F.map n (x : P.M)) v' w')
      (hd v) (hd w))

end DifferentialGeometry.CheegerGromovCompactness
