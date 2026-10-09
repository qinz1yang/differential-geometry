import DifferentialGeometry.Geometry.Geodesic.Naturality.LocalIsometry.Geodesic
import DifferentialGeometry.Geometry.Metric.Pullback.PartialDiffeomorph.Basic
import DifferentialGeometry.Geometry.Metric.Pullback.Local
import DifferentialGeometry.Topology.Manifold.LocalDiffeomorph.OpenCodRestrict
import Mathlib.Analysis.Convex.Contractible
import Mathlib.Topology.Homotopy.Lifting

noncomputable section

open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Riemannian.Geodesic

variable {E F H H' M N X Q : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace H] [TopologicalSpace H']
  {I : ModelWithCorners ℝ E H} {J : ModelWithCorners ℝ F H'}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [TopologicalSpace N] [ChartedSpace H N] [IsManifold I ∞ N] [T2Space N]
  [TopologicalSpace X] [ChartedSpace H' X] [IsManifold J ∞ X] [T2Space X]
  [TopologicalSpace Q] [ChartedSpace H' Q]

omit [FiniteDimensional ℝ E] [FiniteDimensional ℝ F] [IsManifold J ∞ X] [T2Space X] in
private theorem contMDiffAt_lift
    (cover : C(X, Q)) (hcover : IsLocalDiffeomorph J J ∞ cover)
    (α : C(ℝ, Q)) (z : C(ℝ, X))
    (hz : ∀ t, cover (z t) = α t) (t : ℝ)
    (hα : ContMDiffAt 𝓘(ℝ, ℝ) J ∞ α t) :
    ContMDiffAt 𝓘(ℝ, ℝ) J ∞ z t := by
  obtain ⟨Ψ, ht, hΨ⟩ := hcover (z t)
  have htarget : α t ∈ Ψ.target := by
    rw [← hz t, hΨ ht]
    exact Ψ.map_source ht
  have hs := (Ψ.contMDiffOn_invFun.contMDiffAt (Ψ.open_target.mem_nhds htarget)).comp t hα
  apply hs.congr_of_eventuallyEq
  filter_upwards [z.continuous.continuousAt.preimage_mem_nhds (Ψ.open_source.mem_nhds ht)] with s hs
  change z s = Ψ.symm (α s)
  rw [← hz s, hΨ hs]
  exact (Ψ.left_inv hs).symm


variable [I.Boundaryless] [J.Boundaryless]

theorem exists_inverse_curve_lift
    (gTarget : SmoothRiemannianMetric I N) (Φ : PartialDiffeomorph I I M N ∞)
    (χ : PartialDiffeomorph J I Q M ∞)
    (q : C(X, M)) (hq : IsLocalDiffeomorph J I ∞ q)
    (cover : C(X, Q)) (hcover : IsCoveringMap cover)
    (hcover_smooth : IsLocalDiffeomorph J J ∞ cover)
    (hχ : ∀ x, χ (cover x) = q x)
    (γ : C(ℝ, N)) (htarget : ∀ t, γ t ∈ Φ.target)
    (hcusp : ∀ t, Φ.symm (γ t) ∈ χ.target)
    (z₀ : X) (hz₀ : cover z₀ = χ.symm (Φ.symm (γ 0))) (s : Set ℝ)
    (hγ : ∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) I ∞ γ t)
    (hgeo : IsGeodesicOn gTarget γ s)
    (hunit : ∀ t ∈ s,
      gTarget.inner (γ t) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) (mfderiv 𝓘(ℝ, ℝ) I γ t 1) = 1) :
    let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
    let U : TopologicalSpace.Opens X := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
    let qU : U → S := fun x => ⟨q x, x.property⟩
    let hqU : IsLocalDiffeomorph J I ∞ qU := fun x =>
      isLocalDiffeomorphAt_subtypeCodRestrict (fun y => y.property)
        ((isLocalDiffeomorph_comp hq (isLocalDiffeomorph_subtype_val U)) x)
    let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
    ∃ ℓ : C(ℝ, U),
      (ℓ 0 : X) = z₀ ∧
      (∀ t, cover (ℓ t) = χ.symm (Φ.symm (γ t))) ∧
      (∀ t, q (ℓ t) = Φ.symm (γ t)) ∧
      (∀ t ∈ s, ContMDiffAt 𝓘(ℝ, ℝ) J ∞ ℓ t) ∧
      IsGeodesicOn h ℓ s ∧
      (∀ t ∈ s, h.inner (ℓ t) (mfderiv 𝓘(ℝ, ℝ) J ℓ t 1)
        (mfderiv 𝓘(ℝ, ℝ) J ℓ t 1) = 1) := by
  let β : C(ℝ, M) := ⟨fun t => Φ.symm (γ t), by
    apply continuous_iff_continuousAt.mpr
    intro t
    exact (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds (htarget t))).continuousAt.comp
      γ.continuous.continuousAt⟩
  let α : C(ℝ, Q) := ⟨fun t => χ.symm (β t), by
    apply continuous_iff_continuousAt.mpr
    intro t
    change ContinuousAt ((χ.symm : M → Q) ∘ (β : ℝ → M)) t
    have hout : ContinuousAt (χ.symm : M → Q) (β t) :=
      (χ.contMDiffOn_invFun.contMDiffAt (χ.open_target.mem_nhds (hcusp t))).continuousAt
    exact ContinuousAt.comp (f := (β : ℝ → M)) (g := (χ.symm : M → Q)) hout
      β.continuous.continuousAt⟩
  obtain ⟨z, ⟨hzbase, hz⟩, _⟩ := hcover.existsUnique_continuousMap_lifts α 0 z₀ hz₀
  have hzpoint (t : ℝ) : cover (z t) = α t := congrFun hz t
  have hqz (t : ℝ) : q (z t) = β t := by
    rw [← hχ, hzpoint]
    exact χ.right_inv (hcusp t)
  have hzsm (t : ℝ) (ht : t ∈ s) :
      ContMDiffAt 𝓘(ℝ, ℝ) J ∞ z t := by
    apply contMDiffAt_lift cover hcover_smooth α z hzpoint t
    have hβsm : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ β t :=
      (Φ.contMDiffOn_invFun.contMDiffAt (Φ.open_target.mem_nhds (htarget t))).comp t (hγ t ht)
    change ContMDiffAt 𝓘(ℝ, ℝ) J ∞ ((χ.symm : M → Q) ∘ (β : ℝ → M)) t
    exact (χ.contMDiffOn_invFun.contMDiffAt (χ.open_target.mem_nhds (hcusp t))).comp t hβsm
  let S : TopologicalSpace.Opens M := ⟨Φ.source, Φ.open_source⟩
  let U : TopologicalSpace.Opens (X) := ⟨q ⁻¹' S, S.isOpen.preimage q.continuous⟩
  let qU : U → S := fun x => ⟨q x, x.property⟩
  have hqU : IsLocalDiffeomorph J I ∞ qU := fun x =>
    isLocalDiffeomorphAt_subtypeCodRestrict (fun y => y.property)
      ((isLocalDiffeomorph_comp hq (isLocalDiffeomorph_subtype_val U)) x)
  let h := localPullMetric (PartialDiffeomorph.pullbackMetricOn Φ S Set.Subset.rfl gTarget) qU hqU
  have hzU (t : ℝ) : z t ∈ U := by
    change q (z t) ∈ Φ.source
    rw [hqz]
    exact Φ.map_target (htarget t)
  let ℓ : C(ℝ, U) := ⟨fun t => ⟨z t, hzU t⟩, z.continuous.subtype_mk _⟩
  have hℓsm (t : ℝ) (ht : t ∈ s) :
      ContMDiffAt 𝓘(ℝ, ℝ) J ∞ ℓ t :=
    codRestr_contMDiffAt hzU (hzsm t ht)
  let fS : S → N := fun x => Φ (x : M)
  have hfS : IsLocalDiffeomorph I I ∞ fS :=
    isLocalDiffeomorph_restrict_open S (fun x => Φ.isLocalDiffeomorphAt I I ∞ x.property)
  let F : U → N := fS ∘ qU
  have hF : IsLocalDiffeomorph J I ∞ F := isLocalDiffeomorph_comp hfS hqU
  have hfSderiv (x : S) (u : TangentSpace I x) :
      mfderiv I I fS x u = mfderiv I I Φ (x : M) u := by
    have hd := mfderiv_comp_apply x (Φ.mdifferentiableAt (by simp) x.property)
      ((isLocalDiffeomorph_subtype_val S).contMDiff.mdifferentiableAt (by simp)) u
    rw [mfderiv_subtype_val_apply] at hd
    exact hd
  have hmetric (x : U) (v w : TangentSpace J x) :
      h.inner x v w = gTarget.inner (F x) (mfderiv J I F x v) (mfderiv J I F x w) := by
    have hd (u : TangentSpace J x) : mfderiv J I F x u =
        mfderiv I I Φ (q x) (mfderiv J I qU x u) := by
      rw [mfderiv_comp_apply x (hfS.contMDiff.mdifferentiableAt (by simp))
        (hqU.contMDiff.mdifferentiableAt (by simp)), hfSderiv]
    change (localPullMetric _ qU hqU).inner x v w = _
    rw [localPullMetric_inner, PartialDiffeomorph.pullbackMetricOn_inner, hd, hd]
    rfl
  have hFℓ : (fun t => F (ℓ t)) = γ := by
    funext t
    change Φ (q (z t)) = γ t
    rw [hqz]
    exact Φ.right_inv (htarget t)
  have hgeolift : IsGeodesicOn h ℓ (s) := by
    intro t ht
    apply geoEq_of_map_localIso h gTarget hF hmetric ℓ t (hℓsm t ht)
    simpa only [hFℓ] using hgeo t ht
  have hunitlift (t : ℝ) (ht : t ∈ s) :
      h.inner (ℓ t) (mfderiv 𝓘(ℝ, ℝ) J ℓ t 1) (mfderiv 𝓘(ℝ, ℝ) J ℓ t 1) = 1 := by
    have hd := mfderiv_comp_apply t (hF.contMDiff.mdifferentiableAt (by simp))
      ((hℓsm t ht).mdifferentiableAt (by simp)) (1 : ℝ)
    change mfderiv 𝓘(ℝ, ℝ) I (fun t => F (ℓ t)) t 1 = _ at hd
    rw [hFℓ] at hd
    rw [hmetric]
    have hgt : F (ℓ t) = γ t := congrFun hFℓ t
    change gTarget.inner (F (ℓ t))
      (mfderiv J I F (ℓ t) (mfderiv 𝓘(ℝ, ℝ) J ℓ t 1))
      (mfderiv J I F (ℓ t) (mfderiv 𝓘(ℝ, ℝ) J ℓ t 1)) = 1
    exact (congrArg₂ (fun v w : TangentSpace I (F (ℓ t)) => gTarget.inner (F (ℓ t)) v w)
      hd.symm hd.symm).trans
      ((congrArg (fun y : N => gTarget.inner y
        (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : E) (mfderiv 𝓘(ℝ, ℝ) I γ t 1 : E)) hgt).trans
          (hunit t ht))
  exact ⟨ℓ, hzbase, hzpoint, hqz, hℓsm, hgeolift, hunitlift⟩

end DifferentialGeometry.Geometry.Riemannian.Geodesic
