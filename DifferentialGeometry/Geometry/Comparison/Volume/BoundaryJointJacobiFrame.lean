import DifferentialGeometry.Geometry.Comparison.Volume.BoundaryFlowJacobiRegularity

/-!
Actual velocity derivatives of a jointly smooth geodesic family form smooth Jacobi fields.
Local smooth clamps derive the equation on its genuine open velocity-time domain.
-/

set_option autoImplicit false

noncomputable section

open Bundle Filter Manifold Set TopologicalSpace
open scoped Manifold ContDiff Topology
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong

namespace DifferentialGeometry.Geometry.Riemannian.VolumeComparison

variable {E : Type*} [ambientNorm : NormedAddCommGroup E]
  [ambientSpace : NormedSpace ℝ E] [ambientFinite : FiniteDimensional ℝ E]
  {H : Type*} [modelTopology : TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [modelBoundaryless : I.Boundaryless]
  {N : Type*} [interiorTopology : TopologicalSpace N] [interiorCharts : ChartedSpace H N]
  [interiorSmooth : IsManifold I ∞ N] [interiorT2 : T2Space N]

noncomputable def boundaryJointJacobiLinear (F : E × ℝ → N) (v : E) (t : ℝ) :
    E →L[ℝ] TangentSpace I (F (v, t)) :=
  mfderiv 𝓘(ℝ, E) I (fun u => F (u, t)) v

omit ambientFinite modelBoundaryless interiorT2 in
theorem boundaryJointJacobiLinear_smoothAt (V : Opens (E × ℝ)) (F : E × ℝ → N)
    (hF : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ F V) (v w : E) (t : ℝ)
    (ht : (v, t) ∈ V) :
    ContMDiffAt 𝓘(ℝ) I.tangent ∞
      (fun r => (⟨F (v, r), boundaryJointJacobiLinear (I := I) F v r w⟩ :
        TangentBundle I N)) t := by
  let K := 𝓘(ℝ, E).prod 𝓘(ℝ)
  let L : ℝ → TangentBundle K (E × ℝ) := fun r => ⟨(v, r), (w, 0)⟩
  have hL : ContMDiff 𝓘(ℝ) K.tangent ∞ L := by
    have hzero : ContMDiff 𝓘(ℝ) (𝓘(ℝ)).tangent ∞
        (fun r : ℝ => (⟨r, 0⟩ : TangentBundle 𝓘(ℝ) ℝ)) :=
      Bundle.contMDiff_zeroSection ℝ (TangentSpace 𝓘(ℝ) : ℝ → Type _)
    have hpair : ContMDiff 𝓘(ℝ) ((𝓘(ℝ, E)).tangent.prod (𝓘(ℝ)).tangent) ∞
        (fun r : ℝ => ((⟨v, w⟩ : TangentBundle 𝓘(ℝ, E) E),
          (⟨r, 0⟩ : TangentBundle 𝓘(ℝ) ℝ))) :=
      contMDiff_const.prodMk hzero
    exact (contMDiff_equivTangentBundleProd_symm
      (I := 𝓘(ℝ, E)) (I' := 𝓘(ℝ)) (M := E) (M' := ℝ)).comp hpair
  have hmap : ContMDiffOn K.tangent I.tangent ∞ (tangentMapWithin K I F V)
      ((TotalSpace.proj : TangentBundle K (E × ℝ) → E × ℝ) ⁻¹' V) :=
    hF.contMDiffOn_tangentMapWithin (by simp) V.isOpen.uniqueMDiffOn
  have hopen : IsOpen ((TotalSpace.proj : TangentBundle K (E × ℝ) → E × ℝ) ⁻¹' V) :=
    V.isOpen.preimage
      (contMDiff_proj (n := ∞) (IB := K) (TangentSpace K : (E × ℝ) → Type _)).continuous
  have hQ : ContMDiffAt 𝓘(ℝ) I.tangent ∞
      (fun r => tangentMapWithin K I F V (L r)) t :=
    (hmap.contMDiffAt (hopen.mem_nhds ht)).comp (f := L) t hL.contMDiffAt
  have hnear : ∀ᶠ r in 𝓝 t, (v, r) ∈ V :=
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds ht
  have hev : (fun r => tangentMapWithin K I F V (L r)) =ᶠ[𝓝 t]
      (fun r => (⟨F (v, r), boundaryJointJacobiLinear (I := I) F v r w⟩ :
        TangentBundle I N)) := by
    filter_upwards [hnear] with r hr
    have hfull : MDifferentiableAt K I F (v, r) :=
      (hF.contMDiffAt (V.isOpen.mem_nhds hr)).mdifferentiableAt (by simp)
    have hwithin := tangentMapWithin_eq_tangentMap (p := L r)
      (V.isOpen.uniqueMDiffOn (v, r) hr) hfull
    rw [hwithin]
    have hincl : HasMFDerivAt 𝓘(ℝ, E) K (fun u : E => (u, r)) v
        ((ContinuousLinearMap.id ℝ E).prod (0 : E →L[ℝ] ℝ)) :=
      (hasMFDerivAt_id v).prodMk (hasMFDerivAt_const r v)
    have hcomp := mfderiv_comp v hfull hincl.mdifferentiableAt
    rw [hincl.mfderiv] at hcomp
    have happ := congrArg (fun A : E →L[ℝ] E => A w) hcomp
    have hvalue : (mfderiv 𝓘(ℝ, E) I (fun u : E => F (u, r)) v w : E) =
        mfderiv K I F (v, r) (w, 0) := happ
    apply TotalSpace.ext
    · rfl
    · exact heq_of_eq hvalue.symm
  exact hQ.congr_of_eventuallyEq hev.symm

omit ambientFinite modelBoundaryless interiorSmooth interiorT2 in
private theorem jointLinear_angular (V : Opens (E × ℝ)) (F : E × ℝ → N)
    (hF : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ F V) (v w : E) (t : ℝ)
    (ht : (v, t) ∈ V) :
    (mfderiv 𝓘(ℝ) I (fun s : ℝ => F (v + s • w, t)) 0 (1 : ℝ) : E) =
      boundaryJointJacobiLinear (I := I) F v t w := by
  have hpoint : ContMDiffAt 𝓘(ℝ, E) I ∞ (fun u : E => F (u, t)) v :=
    (hF.contMDiffAt (V.isOpen.mem_nhds ht)).comp (f := fun u : E => (u, t)) v
      (contMDiffAt_id.prodMk contMDiffAt_const)
  have hline : HasDerivAt (fun s : ℝ => v + s • w) w 0 := by
    simpa only [id_eq, one_smul] using
      ((hasDerivAt_id (0 : ℝ)).smul_const w).const_add v
  have hlineMF := hline.hasFDerivAt.hasMFDerivAt
  have hlineApplied : (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s : ℝ => v + s • w)
      0 (1 : ℝ) : E) = w := by
    have hh := congrArg (fun A : ℝ →L[ℝ] E => A (1 : ℝ)) hlineMF.mfderiv
    change (mfderiv 𝓘(ℝ) 𝓘(ℝ, E) (fun s : ℝ => v + s • w)
      0 (1 : ℝ) : E) = (1 : ℝ) • w at hh
    exact hh.trans (one_smul ℝ w)
  have hchain := mfderiv_comp_apply_of_eq (0 : ℝ)
    (hpoint.mdifferentiableAt (by simp)) hlineMF.mdifferentiableAt
    (show v + (0 : ℝ) • w = v by simp only [zero_smul, add_zero]) (1 : ℝ)
  rw [hlineApplied] at hchain
  exact hchain

theorem boundaryJointJacobiLinear_jacobi (g : SmoothRiemannianMetric I N)
    (V : Opens (E × ℝ)) (F : E × ℝ → N)
    (hF : ContMDiffOn (𝓘(ℝ, E).prod 𝓘(ℝ)) I ∞ F V)
    (hgeo : ∀ q ∈ V, HasGeodesicEquationAt g (fun r => F (q.1, r)) q.2)
    (v w : E) (t : ℝ) (ht : (v, t) ∈ V) :
    IsJacobiAt g (fun r => F (v, r))
      (fun r => boundaryJointJacobiLinear (I := I) F v r w) t ∧
    ContMDiffAt 𝓘(ℝ) I.tangent ∞
      (fun r => (⟨F (v, r), boundaryJointJacobiLinear (I := I) F v r w⟩ :
        TangentBundle I N)) t := by
  refine ⟨?_, boundaryJointJacobiLinear_smoothAt V F hF v w t ht⟩
  let K := 𝓘(ℝ).prod 𝓘(ℝ)
  let A : ℝ × ℝ → E × ℝ := fun q => (v + q.1 • w, q.2)
  let D : Set (ℝ × ℝ) := A ⁻¹' V
  let Fs : ℝ × ℝ → N := fun q => F (A q)
  have hline : ContMDiff 𝓘(ℝ) 𝓘(ℝ, E) ∞ (fun s : ℝ => v + s • w) :=
    (contDiff_const.add (contDiff_id.smul contDiff_const)).contMDiff
  have hA : ContMDiff K (𝓘(ℝ, E).prod 𝓘(ℝ)) ∞ A :=
    (hline.comp contMDiff_fst).prodMk contMDiff_snd
  have hDopen : IsOpen D := V.isOpen.preimage hA.continuous
  have hDzero : (0, t) ∈ D := by
    change (v + (0 : ℝ) • w, t) ∈ V
    simpa only [zero_smul, add_zero] using ht
  have hFs : ContMDiffOn K I ∞ Fs D := hF.comp hA.contMDiffOn (fun q hq => hq)
  obtain ⟨φ, ψ, hφ, hψ, hφid, hψid, hrange⟩ :=
    DifferentialGeometry.exists_contDiff_prodMap_range_subset (hDopen.mem_nhds hDzero)
  let Fhat : ℝ → ℝ → N := fun s r => Fs (φ s, ψ r)
  have hψtime : ψ t = t := hψid.eq_of_nhds
  have hphase : ContMDiff K K ∞ (fun q : ℝ × ℝ => (φ q.1, ψ q.2)) :=
    (hφ.contMDiff.comp contMDiff_fst).prodMk (hψ.contMDiff.comp contMDiff_snd)
  have hFhat : ContMDiff K I ∞ (fun q : ℝ × ℝ => Fhat q.1 q.2) := by
    intro q
    have hq : (φ q.1, ψ q.2) ∈ D := hrange ⟨q, rfl⟩
    exact (hFs.contMDiffAt (hDopen.mem_nhds hq)).comp
      (f := fun z : ℝ × ℝ => (φ z.1, ψ z.2)) q hphase.contMDiffAt
  have hvariation : IsSmoothVariation Fhat := hFhat.of_le ENat.LEInfty.out
  have hzero : ∀ s : ℝ, covDerivAlong g (fun r => Fhat s r)
      (fun r => mfderiv 𝓘(ℝ) I (fun u => Fhat s u) r 1) t = 0 := by
    intro s
    have hdom : (φ s, t) ∈ D := by
      have hd : (φ s, ψ t) ∈ D := hrange ⟨(s, t), rfl⟩
      rwa [hψtime] at hd
    have hg := hgeo (v + φ s • w, t) hdom
    have hev : (fun r => Fhat s r) =ᶠ[𝓝 t] (fun r => F (v + φ s • w, r)) := by
      filter_upwards [hψid] with r hr
      simp only [Fhat, Fs, A, hr, id_eq]
    have hgeoHat := HasGeodesicEquationAt.congr_of_eventuallyEq_at hev.eq_of_nhds hev hg
    have hslice : ContMDiffAt 𝓘(ℝ) I 2 (fun r => Fhat s r) t :=
      (hFhat.comp (contMDiff_const.prodMk contMDiff_id)).contMDiffAt.of_le (by norm_num)
    exact covDerivAlong_velocity_eq_zero_of_hasGeodesicEquationAt_C2 g _ t hslice hgeoHat
  have hjac := isJacobiAt_variationField_of_covDerivAlong_velocity_eq_zero
    g Fhat hvariation t hzero
  have hnear : ∀ᶠ r in 𝓝 t, (v, r) ∈ V :=
    (V.isOpen.preimage (continuous_const.prodMk continuous_id)).mem_nhds ht
  have hfield : (fun r => (⟨Fhat 0 r,
      mfderiv 𝓘(ℝ) I (fun s => Fhat s r) 0 1⟩ : TangentBundle I N)) =ᶠ[𝓝 t]
      (fun r => (⟨F (v, r), boundaryJointJacobiLinear (I := I) F v r w⟩ :
        TangentBundle I N)) := by
    filter_upwards [hψid, hnear] with r hr hvr
    have hspatial : (fun s => Fhat s r) =ᶠ[𝓝 (0 : ℝ)]
        (fun s : ℝ => F (v + s • w, r)) := by
      filter_upwards [hφid] with s hs
      simp only [Fhat, Fs, A, hs, hr, id_eq]
    have hder : mfderiv 𝓘(ℝ) I (fun s => Fhat s r) 0 =
        mfderiv 𝓘(ℝ) I (fun s : ℝ => F (v + s • w, r)) 0 := hspatial.mfderiv_eq
    have happ := congrArg (fun L : ℝ →L[ℝ] E => L (1 : ℝ)) hder
    have hvalue := happ.trans (jointLinear_angular V F hF v w r hvr)
    apply TotalSpace.ext
    · exact hspatial.eq_of_nhds.trans
        (congrArg (fun u : E => F (u, r)) (show v + (0 : ℝ) • w = v by simp))
    · exact heq_of_eq hvalue
  exact hjac.congr_of_eventuallyEq hfield

end DifferentialGeometry.Geometry.Riemannian.VolumeComparison
