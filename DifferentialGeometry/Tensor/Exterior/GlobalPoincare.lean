import DifferentialGeometry.Tensor.Exterior.Poincare
import Mathlib.Topology.Sheaves.EtaleSpace
import Mathlib.Topology.Sheaves.LocalPredicate
import Mathlib.Topology.Homotopy.Lifting

set_option autoImplicit false

noncomputable section

open Bundle Set Function Filter CategoryTheory
open scoped Topology Manifold ContDiff

namespace DifferentialGeometry.DifferentialForm

universe uE uH uM

variable {E : Type uE} [NormedAddCommGroup E] [NormedSpace ℝ E]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners ℝ E H} [I.Boundaryless]
variable {M : Type uM} [TopologicalSpace M] [ChartedSpace H M]
variable [IsManifold I ∞ M]

private theorem eventuallyEq_const_of_mvfderiv_eq_zero
    {f : M → ℝ} {U : Set M} (hU : IsOpen U) {x : M} (hxU : x ∈ U)
    (hf : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ f U)
    (hdf : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) f y v = 0) :
    f =ᶠ[𝓝 x] fun _ => f x := by
  let z0 : E := extChartAt I x x
  have htarget : (extChartAt I x).target ∈ 𝓝 z0 :=
    (isOpen_extChartAt_target x).mem_nhds (mem_extChartAt_target x)
  have hUcoord : (extChartAt I x).symm ⁻¹' U ∈ 𝓝 z0 := by
    apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
    simpa only [z0, (extChartAt I x).left_inv (mem_extChartAt_source x)] using
      hU.mem_nhds hxU
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp (inter_mem htarget hUcoord)
  let B : Set E := Metric.ball z0 r
  let q : E → ℝ := f ∘ (extChartAt I x).symm
  have hBtarget : B ⊆ (extChartAt I x).target := fun z hz =>
    (hball (by simpa only [B] using hz)).1
  have hBU : ∀ z ∈ B, (extChartAt I x).symm z ∈ U := fun z hz =>
    (hball (by simpa only [B] using hz)).2
  have hqdiff : DifferentiableOn ℝ q B := by
    intro z hz
    let y := (extChartAt I x).symm z
    have hytarget : z ∈ (extChartAt I x).target := hBtarget hz
    have hyU : y ∈ U := hBU z hz
    have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm z :=
      (mdifferentiableWithinAt_extChartAt_symm hytarget).mdifferentiableAt
        (by simp [I.range_eq_univ])
    have hfAt : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
      ((hf y hyU).contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp)
    have hqAt : MDifferentiableAt 𝓘(ℝ, E) 𝓘(ℝ, ℝ) q z :=
      hfAt.comp z hsymm
    exact hqAt.differentiableAt.differentiableWithinAt
  have hqderiv : ∀ z ∈ B, fderiv ℝ q z = 0 := by
    intro z hz
    let y := (extChartAt I x).symm z
    have hytarget : z ∈ (extChartAt I x).target := hBtarget hz
    have hyU : y ∈ U := hBU z hz
    have hsymm : MDifferentiableAt 𝓘(ℝ, E) I (extChartAt I x).symm z :=
      (mdifferentiableWithinAt_extChartAt_symm hytarget).mdifferentiableAt
        (by simp [I.range_eq_univ])
    have hfAt : MDifferentiableAt I 𝓘(ℝ, ℝ) f y :=
      ((hf y hyU).contMDiffAt (hU.mem_nhds hyU)).mdifferentiableAt (by simp)
    apply ContinuousLinearMap.ext
    intro w
    let v : TangentSpace 𝓘(ℝ, E) z :=
      (tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) z).symm w
    have hchain := mvfderiv_comp_apply z hfAt hsymm v
    have hzero := hdf y hyU
      (mfderiv 𝓘(ℝ, E) I (extChartAt I x).symm z v)
    rw [hzero] at hchain
    have hmodel := mvfderiv_model_apply_eq_fderiv (f := q) v
    rw [hchain] at hmodel
    have hv : tangentSpaceModelContinuousLinearEquiv (I := 𝓘(ℝ, E)) z v = w :=
      ContinuousLinearEquiv.apply_symm_apply _ w
    rw [hv] at hmodel
    change fderiv ℝ q z w = 0
    exact hmodel.symm
  have hconst : ∀ z ∈ B, q z = q z0 := by
    intro z hz
    exact (convex_ball z0 r).is_const_of_fderivWithin_eq_zero hqdiff
      (fun y hy => by
        rw [fderivWithin_of_isOpen Metric.isOpen_ball hy, hqderiv y hy]) hz
      (Metric.mem_ball_self hr)
  have hpre : (extChartAt I x).source ∩ (extChartAt I x) ⁻¹' B ∈ 𝓝 x :=
    (isOpen_extChartAt_preimage' x Metric.isOpen_ball).mem_nhds
      ⟨mem_extChartAt_source x, Metric.mem_ball_self hr⟩
  filter_upwards [hpre] with y hy
  have hyright : (extChartAt I x).symm (extChartAt I x y) = y :=
    (extChartAt I x).left_inv hy.1
  have hxright : (extChartAt I x).symm z0 = x :=
    (extChartAt I x).left_inv (mem_extChartAt_source x)
  simpa only [q, Function.comp_apply, hyright, hxright] using hconst _ hy.2

private def potentialPrelocal (alpha : DifferentialForm I M 1) :
    TopCat.PrelocalPredicate (X := TopCat.of M) (fun _ => ULift.{uM} ℝ) where
  pred {U} f :=
    ∃ F : M → ℝ,
      ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F U ∧
      (∀ y ∈ U, ∀ v : TangentSpace I y,
        mvfderiv (I := I) F y v = alpha y (fun _ : Fin 1 => v)) ∧
      ∀ y : U, f y = ULift.up (F y)
  res {U V} i f hf := by
    obtain ⟨F, hFsmooth, hFd, hFval⟩ := hf
    refine ⟨F, hFsmooth.mono i.le, ?_, ?_⟩
    · intro y hy v
      exact hFd y (i.le hy) v
    · intro y
      exact hFval ⟨y, i.le y.2⟩

private def potentialLocal (alpha : DifferentialForm I M 1) :
    TopCat.LocalPredicate (X := TopCat.of M) (fun _ => ULift.{uM} ℝ) :=
  (potentialPrelocal alpha).sheafify

omit [I.Boundaryless] in
private theorem potentialLocal_of_potentialOn
    (alpha : DifferentialForm I M 1) {U : TopologicalSpace.Opens (TopCat.of M)}
    (F : M → ℝ) (hFsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F U)
    (hFd : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) F y v = alpha y (fun _ : Fin 1 => v)) :
    (potentialLocal alpha).pred (fun y : U => ULift.up (F y)) := by
  exact TopCat.PrelocalPredicate.sheafifyOf ⟨F, hFsmooth, hFd, fun _ => rfl⟩

private theorem potentialLocal_sub_eventuallyEq
    (alpha : DifferentialForm I M 1) {U : TopologicalSpace.Opens (TopCat.of M)}
    {f g : ∀ _ : U, ULift.{uM} ℝ} (hf : (potentialLocal alpha).pred f)
    (hg : (potentialLocal alpha).pred g) (x : U) :
    (fun y => (f y).down - (g y).down) =ᶠ[𝓝 x]
      fun _ => (f x).down - (g x).down := by
  obtain ⟨V, hxV, iV, hV⟩ := hf x
  obtain ⟨F, hFsmooth, hFd, hFval⟩ := hV
  obtain ⟨W, hxW, iW, hW⟩ := hg x
  obtain ⟨G, hGsmooth, hGd, hGval⟩ := hW
  have hFx : f x = ULift.up (F x) := by
    convert hFval ⟨x.1, hxV⟩ using 1
    change f x = f ⟨x.1, iV.le hxV⟩
    congr
  have hGx : g x = ULift.up (G x) := by
    convert hGval ⟨x.1, hxW⟩ using 1
    change g x = g ⟨x.1, iW.le hxW⟩
    congr
  let D : M → ℝ := F - G
  have hDsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ D (V ∩ W) :=
    (hFsmooth.mono inter_subset_left).sub (hGsmooth.mono inter_subset_right)
  have hDd : ∀ y ∈ (V : Set M) ∩ W, ∀ v : TangentSpace I y,
      mvfderiv (I := I) D y v = 0 := by
    intro y hy v
    have hFAt : MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
      (((hFsmooth y hy.1).contMDiffAt (V.isOpen.mem_nhds hy.1)).mdifferentiableAt
        (by simp))
    have hGAt : MDifferentiableAt I 𝓘(ℝ, ℝ) G y :=
      (((hGsmooth y hy.2).contMDiffAt (W.isOpen.mem_nhds hy.2)).mdifferentiableAt
        (by simp))
    rw [show D = F - G from rfl, mvfderiv_sub hFAt hGAt]
    change (mvfderiv (I := I) F y) v - (mvfderiv (I := I) G y) v = 0
    rw [hFd y hy.1 v, hGd y hy.2 v, sub_self]
  have hDlocal := eventuallyEq_const_of_mvfderiv_eq_zero
    (V.isOpen.inter W.isOpen) ⟨hxV, hxW⟩ hDsmooth hDd
  have hVnhds : {y : U | y.1 ∈ V} ∈ 𝓝 x :=
    (V.isOpen.preimage continuous_subtype_val).mem_nhds hxV
  have hWnhds : {y : U | y.1 ∈ W} ∈ 𝓝 x :=
    (W.isOpen.preimage continuous_subtype_val).mem_nhds hxW
  filter_upwards [continuousAt_subtype_val.eventually hDlocal, hVnhds, hWnhds]
    with y hDy hyV hyW
  have hFy : f y = ULift.up (F y) := by
    convert hFval ⟨y.1, hyV⟩ using 1
    change f y = f ⟨y.1, iV.le hyV⟩
    congr
  have hGy : g y = ULift.up (G y) := by
    convert hGval ⟨y.1, hyW⟩ using 1
    change g y = g ⟨y.1, iW.le hyW⟩
    congr
  have hFydown : (f y).down = F y := congrArg ULift.down hFy
  have hGydown : (g y).down = G y := congrArg ULift.down hGy
  have hFxdown : (f x).down = F x := congrArg ULift.down hFx
  have hGxdown : (g x).down = G x := congrArg ULift.down hGx
  rw [hFydown, hGydown, hFxdown, hGxdown]
  exact hDy

private theorem potentialLocal_sub_isLocallyConstant
    (alpha : DifferentialForm I M 1) {U : TopologicalSpace.Opens (TopCat.of M)}
    {f g : ∀ _ : U, ULift.{uM} ℝ} (hf : (potentialLocal alpha).pred f)
    (hg : (potentialLocal alpha).pred g) :
    IsLocallyConstant fun y => (f y).down - (g y).down :=
  IsLocallyConstant.iff_eventually_eq _ |>.2 fun x =>
    potentialLocal_sub_eventuallyEq alpha hf hg x

private theorem potentialLocal_eventuallyEq
    (alpha : DifferentialForm I M 1) {U : TopologicalSpace.Opens (TopCat.of M)}
    {f g : ∀ _ : U, ULift.{uM} ℝ} (hf : (potentialLocal alpha).pred f)
    (hg : (potentialLocal alpha).pred g) {x : U} (hx : f x = g x) :
    f =ᶠ[𝓝 x] g := by
  have hsub := potentialLocal_sub_eventuallyEq alpha hf hg x
  filter_upwards [hsub] with y hy
  apply ULift.ext
  have hxdown : (f x).down = (g x).down := congrArg ULift.down hx
  have hzero : (f x).down - (g x).down = 0 := sub_eq_zero.mpr hxdown
  exact sub_eq_zero.mp (hy.trans hzero)

private theorem potentialStalkToFiber_bijective
    (alpha : DifferentialForm I M 1) (halpha : isClosed alpha) (x : M) :
    Function.Bijective (TopCat.stalkToFiber (X := TopCat.of M)
      (potentialLocal (I := I) (M := M) alpha) x) := by
  constructor
  · apply TopCat.stalkToFiber_injective (X := TopCat.of M)
    intro U V fU hfU fV hfV hvalue
    let A : TopologicalSpace.Opens (TopCat.of M) := U.1 ⊓ V.1
    let xA : A := ⟨x, U.2, V.2⟩
    let fA : A → ULift.{uM} ℝ := fun z => fU ⟨z.1, z.2.1⟩
    let gA : A → ULift.{uM} ℝ := fun z => fV ⟨z.1, z.2.2⟩
    have hfA : (potentialLocal (I := I) (M := M) alpha).pred fA := by
      exact (potentialLocal (I := I) (M := M) alpha).res
        (TopologicalSpace.Opens.infLELeft _ _) fU hfU
    have hgA : (potentialLocal (I := I) (M := M) alpha).pred gA := by
      exact (potentialLocal (I := I) (M := M) alpha).res
        (TopologicalSpace.Opens.infLERight _ _) fV hfV
    have hxvalue : fA xA = gA xA := by
      simpa only [fA, gA, xA] using hvalue
    have hlocal := potentialLocal_eventuallyEq alpha hfA hgA hxvalue
    obtain ⟨S, hSeq, hSopen, hxS⟩ := mem_nhds_iff.mp hlocal
    let Wset : Set M := Subtype.val '' S
    have hWopen : IsOpen Wset := A.isOpen.isOpenMap_subtype_val S hSopen
    have hxW : x ∈ Wset := ⟨xA, hxS, rfl⟩
    let W : TopologicalSpace.OpenNhds (X := TopCat.of M) x :=
      ⟨⟨Wset, hWopen⟩, hxW⟩
    have hWU : (W.1 : Set M) ⊆ U.1 := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2.1
    have hWV : (W.1 : Set M) ⊆ V.1 := by
      rintro y ⟨z, hz, rfl⟩
      exact z.2.2
    let iU : W ⟶ U := homOfLE hWU
    let iV : W ⟶ V := homOfLE hWV
    refine ⟨W, iU, iV, ?_⟩
    intro w
    obtain ⟨z, hzS, hzw⟩ := w.2
    have hzEq := hSeq hzS
    change fA z = gA z at hzEq
    let wu : U.1 := ⟨w.1, hWU w.2⟩
    let wv : V.1 := ⟨w.1, hWV w.2⟩
    let zu : U.1 := ⟨z.1, z.2.1⟩
    let zv : V.1 := ⟨z.1, z.2.2⟩
    have hwu : wu = zu := Subtype.ext hzw.symm
    have hwv : wv = zv := Subtype.ext hzw.symm
    have hzEq' : fU zu = fV zv := by
      simpa only [fA, gA, zu, zv] using hzEq
    change fU wu = fV wv
    exact (congrArg fU hwu).trans (hzEq'.trans (congrArg fV hwv).symm)
  · apply TopCat.stalkToFiber_surjective (X := TopCat.of M)
    intro t
    obtain ⟨U, F, hUopen, hxU, hFx, hFsmooth, hFd⟩ :=
      exists_local_potential alpha halpha x
    let O : TopologicalSpace.Opens (TopCat.of M) := ⟨U, hUopen⟩
    let N : TopologicalSpace.OpenNhds (X := TopCat.of M) x := ⟨O, hxU⟩
    let G : M → ℝ := F + fun _ => t.down
    have hGsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ G U :=
      hFsmooth.add contMDiffOn_const
    have hGd : ∀ y ∈ U, ∀ v : TangentSpace I y,
        mvfderiv (I := I) G y v = alpha y (fun _ : Fin 1 => v) := by
      intro y hy v
      have hFAt : MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
        (((hFsmooth y hy).contMDiffAt (hUopen.mem_nhds hy)).mdifferentiableAt
          (by simp))
      rw [show G = F + fun _ => t.down from rfl,
        mvfderiv_add hFAt (mdifferentiable_const (c := t.down)).mdifferentiableAt,
        mvfderiv_const, add_zero]
      exact hFd y hy v
    refine ⟨N, fun y : N.1 => ULift.up (G y),
      potentialLocal_of_potentialOn (I := I) (M := M) alpha G hGsmooth hGd, ?_⟩
    apply ULift.ext
    simp only [G, Pi.add_apply, hFx, zero_add]

private theorem potentialSectionEvaluation_bijective
    (alpha : DifferentialForm I M 1) {U : TopologicalSpace.Opens (TopCat.of M)}
    (hU : IsPreconnected (U : Set M)) (F : M → ℝ)
    (hFsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ F U)
    (hFd : ∀ y ∈ U, ∀ v : TangentSpace I y,
      mvfderiv (I := I) F y v = alpha y (fun _ : Fin 1 => v))
    (x : M) (hxU : x ∈ U) :
    Function.Bijective
      (fun s : CategoryTheory.ToType
          ((TopCat.subsheafToTypes (potentialLocal (I := I) (M := M) alpha)).presheaf.obj
            (Opposite.op U)) => s.1 ⟨x, hxU⟩) := by
  constructor
  · intro s t hst
    apply Subtype.ext
    funext y
    apply ULift.ext
    let _ : PreconnectedSpace U := Subtype.preconnectedSpace hU
    have hconst := potentialLocal_sub_isLocallyConstant alpha s.2 t.2
    have hdiff := hconst.apply_eq_of_preconnectedSpace y ⟨x, hxU⟩
    have hxdown : (s.1 ⟨x, hxU⟩).down = (t.1 ⟨x, hxU⟩).down :=
      congrArg ULift.down hst
    exact sub_eq_zero.mp (hdiff.trans (sub_eq_zero.mpr hxdown))
  · intro a
    let G : M → ℝ := F + fun _ => a.down - F x
    have hGsmooth : ContMDiffOn I 𝓘(ℝ, ℝ) ∞ G U :=
      hFsmooth.add contMDiffOn_const
    have hGd : ∀ y ∈ U, ∀ v : TangentSpace I y,
        mvfderiv (I := I) G y v = alpha y (fun _ : Fin 1 => v) := by
      intro y hy v
      have hFAt : MDifferentiableAt I 𝓘(ℝ, ℝ) F y :=
        (((hFsmooth y hy).contMDiffAt (U.isOpen.mem_nhds hy)).mdifferentiableAt
          (by simp))
      rw [show G = F + fun _ => a.down - F x from rfl,
        mvfderiv_add hFAt (mdifferentiable_const (c := a.down - F x)).mdifferentiableAt,
        mvfderiv_const, add_zero]
      exact hFd y hy v
    let s : CategoryTheory.ToType
        ((TopCat.subsheafToTypes (potentialLocal (I := I) (M := M) alpha)).presheaf.obj
          (Opposite.op U)) :=
      ⟨fun y : U => ULift.up (G y),
        potentialLocal_of_potentialOn (I := I) (M := M) alpha G hGsmooth hGd⟩
    refine ⟨s, ?_⟩
    apply ULift.ext
    simp only [s, G, Pi.add_apply]
    ring

private theorem potentialEtaleSpace_isCoveringMap
    (alpha : DifferentialForm I M 1) (halpha : isClosed alpha) :
    IsCoveringMap
      (TopCat.Presheaf.EtaleSpace.base
        (F := (TopCat.subsheafToTypes
          (potentialLocal (I := I) (M := M) alpha)).presheaf)) := by
  let _ : LocallyConnectedSpace H := I.toHomeomorph.locallyConnectedSpace
  let _ : LocallyConnectedSpace M := ChartedSpace.locallyConnectedSpace H M
  apply TopCat.Presheaf.EtaleSpace.isCoveringMap_base
  intro x
  obtain ⟨U, F, hUopen, hxU, hFx, hFsmooth, hFd⟩ :=
    exists_local_potential alpha halpha x
  obtain ⟨V, hVU, hVopen, hxV, hVconnected⟩ :=
    (locallyConnectedSpace_iff_subsets_isOpen_isConnected.mp inferInstance)
      x U (hUopen.mem_nhds hxU)
  let O : TopologicalSpace.Opens (TopCat.of M) := ⟨V, hVopen⟩
  refine ⟨O, hxV, ?_⟩
  intro y hyO
  have heval := potentialSectionEvaluation_bijective (I := I) (M := M) alpha
    hVconnected.isPreconnected F (hFsmooth.mono hVU)
    (fun z hz => hFd z (hVU hz)) y hyO
  have hstalk := potentialStalkToFiber_bijective (I := I) (M := M) alpha halpha y
  constructor
  · intro s t hst
    apply heval.injective
    have h := congrArg
      (TopCat.stalkToFiber (X := TopCat.of M)
        (potentialLocal (I := I) (M := M) alpha) y) hst
    rw [TopCat.stalkToFiber_germ, TopCat.stalkToFiber_germ] at h
    exact h
  · intro q
    let a := TopCat.stalkToFiber (X := TopCat.of M)
      (potentialLocal (I := I) (M := M) alpha) y q
    obtain ⟨s, hs⟩ := heval.surjective a
    refine ⟨s, hstalk.injective ?_⟩
    rw [TopCat.stalkToFiber_germ]
    exact hs

theorem exists_global_potential [SimplyConnectedSpace M]
    (alpha : DifferentialForm I M 1) (halpha : isClosed alpha) :
    ∃ f : M → ℝ,
      ContMDiff I 𝓘(ℝ, ℝ) ∞ f ∧
      ∀ x, ∀ v : TangentSpace I x,
        mvfderiv (I := I) f x v = alpha x (fun _ : Fin 1 => v) := by
  let _ : LocallyPathConnectedSpace H :=
    I.toHomeomorph.isOpenEmbedding.locallyPathConnectedSpace
  let _ : LocallyPathConnectedSpace M :=
    ChartedSpace.locallyPathConnectedSpace H M
  let P := potentialLocal (I := I) (M := M) alpha
  let F := (TopCat.subsheafToTypes P).presheaf
  let x0 : M := Classical.arbitrary M
  obtain ⟨U0, f0, hU0open, hx0U0, hf0x, hf0smooth, hf0d⟩ :=
    exists_local_potential alpha halpha x0
  let O0 : TopologicalSpace.Opens (TopCat.of M) := ⟨U0, hU0open⟩
  let s0 : CategoryTheory.ToType (F.obj (Opposite.op O0)) :=
    ⟨fun y : O0 => ULift.up (f0 y),
      potentialLocal_of_potentialOn (I := I) (M := M) alpha f0 hf0smooth hf0d⟩
  let e0 : TopCat.Presheaf.EtaleSpace F :=
    ⟨x0, F.germ O0 x0 hx0U0 s0⟩
  have hcov : IsCoveringMap
      (TopCat.Presheaf.EtaleSpace.base (F := F)) :=
    potentialEtaleSpace_isCoveringMap (I := I) (M := M) alpha halpha
  obtain ⟨L, hL0, hLproj⟩ :=
    (hcov.existsUnique_continuousMap_lifts (ContinuousMap.id M) x0 e0 rfl).exists
  have hbase (x : M) : (L x).base = x := by
    have h := congrFun hLproj x
    simpa only [Function.comp_apply, ContinuousMap.coe_id, id_eq] using h
  let f : M → ℝ := fun x =>
    (TopCat.stalkToFiber P (L x).base (L x).germ).down
  have hlocal (x : M) :
      ∃ (V : Set M) (G : M → ℝ),
        And (IsOpen V) <| And (x ∈ V) <|
        And (ContMDiffOn I 𝓘(ℝ, ℝ) ∞ G V) <|
        And (∀ y ∈ V, ∀ v : TangentSpace I y,
          mvfderiv (I := I) G y v = alpha y (fun _ : Fin 1 => v)) <|
        ∀ y ∈ V, f y = G y := by
    obtain ⟨U, hxUbase, s, hLsection⟩ :=
      TopCat.Presheaf.EtaleSpace.exists_section_of_tendsto L.continuous.continuousAt
    have hxU : x ∈ U := by
      rw [← hbase x]
      exact hxUbase
    obtain ⟨V, hxV, iV, hV⟩ := s.2 ⟨x, hxU⟩
    obtain ⟨G, hGsmooth, hGd, hGval⟩ := hV
    obtain ⟨A, hAsection, hAopen, hxA⟩ := mem_nhds_iff.mp hLsection
    let W : Set M := V ∩ A
    refine ⟨W, G, V.isOpen.inter hAopen, ⟨hxV, hxA⟩,
      hGsmooth.mono inter_subset_left, (fun y hy => hGd y hy.1), ?_⟩
    intro y hy
    obtain ⟨hyUbase, hygerm⟩ := hAsection hy.2
    have hyU : y ∈ U := by
      rw [← hbase y]
      exact hyUbase
    have hsectionValue : s.1 ⟨y, hyU⟩ = ULift.up (G y) := by
      have h := hGval ⟨y, hy.1⟩
      convert h using 1
      · change s.1 ⟨y, hyU⟩ = s.1 ⟨y, iV.le hy.1⟩
        congr
    dsimp only [f]
    have hvalue := TopCat.stalkToFiber_germ P U (L y).base hyUbase s
    rw [← hygerm] at hvalue
    have hpoint : (⟨(L y).base, hyUbase⟩ : U) = ⟨y, hyU⟩ := Subtype.ext (hbase y)
    rw [hpoint, hsectionValue] at hvalue
    exact congrArg ULift.down hvalue
  have hfsmooth : ContMDiff I 𝓘(ℝ, ℝ) ∞ f := by
    apply contMDiff_of_locally_contMDiffOn
    intro x
    obtain ⟨V, G, hVopen, hxV, hGsmooth, hGd, hfeq⟩ := hlocal x
    refine ⟨V, hVopen, hxV, ?_⟩
    exact hGsmooth.congr fun y hy => hfeq y hy
  refine ⟨f, hfsmooth, ?_⟩
  intro x v
  obtain ⟨V, G, hVopen, hxV, hGsmooth, hGd, hfeq⟩ := hlocal x
  have hevent : f =ᶠ[𝓝 x] G := by
    filter_upwards [hVopen.mem_nhds hxV] with y hy
    exact hfeq y hy
  have hmv : mvfderiv (I := I) f x = mvfderiv (I := I) G x := by
    change
      (NormedSpace.fromTangentSpace (f x)).toContinuousLinearMap ∘L
          mfderiv I 𝓘(ℝ, ℝ) f x =
        (NormedSpace.fromTangentSpace (G x)).toContinuousLinearMap ∘L
          mfderiv I 𝓘(ℝ, ℝ) G x
    rw [hevent.self_of_nhds,
      Filter.EventuallyEq.mfderiv_eq
        (I := I) (I' := 𝓘(ℝ, ℝ)) hevent]
  rw [hmv]
  exact hGd x hxV v

end DifferentialGeometry.DifferentialForm
