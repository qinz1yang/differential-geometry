import DifferentialGeometry.Tensor.Exterior.Exact
import DifferentialGeometry.Analysis.Calculus.Potential

noncomputable section

open Bundle Set ContinuousAlternatingMap Function Filter
open scoped Topology Manifold ContDiff Bundle

namespace DifferentialGeometry
namespace DifferentialForm

attribute [local instance] seminormedAddCommGroupTangentSpace
attribute [local instance] normedAddCommGroupTangentSpace
attribute [local instance] normedSpaceTangentSpace

private theorem oneForm_fderiv_symm
    {E : Type*} [NormedAddCommGroup E] [NormedSpace Real E]
    (rep : E → E [⋀^Fin 1]→L[Real] Real) (z : E)
    (hrep : DifferentiableAt Real rep z) (hzero : extDeriv rep z = 0) :
    ∀ v w : E,
      fderiv Real (fun y =>
        (ofSubsingletonLIE (𝕜 := Real) (E := E) (F := Real) (0 : Fin 1)).symm (rep y)) z v w =
        fderiv Real (fun y =>
          (ofSubsingletonLIE (𝕜 := Real) (E := E) (F := Real) (0 : Fin 1)).symm (rep y)) z w v := by
  let omega : E → E →L[Real] Real :=
    fun y => (ofSubsingletonLIE (𝕜 := Real) (E := E) (F := Real) (0 : Fin 1)).symm (rep y)
  have homega : HasFDerivAt omega
      ((ofSubsingletonLIE (𝕜 := Real) (E := E) (F := Real)
        (0 : Fin 1)).symm.toLinearIsometry.toContinuousLinearMap.comp
        (fderiv Real rep z)) z :=
    (ofSubsingletonLIE (𝕜 := Real) (E := E) (F := Real)
      (0 : Fin 1)).symm.toLinearIsometry.toContinuousLinearMap.hasFDerivAt.comp z
      hrep.hasFDerivAt
  intro v w
  have hext := congrArg (fun L : E [⋀^Fin 2]→L[Real] Real => L ![v, w]) hzero
  rw [extDeriv_apply hrep ![v, w]] at hext
  have hremove0 : (Fin.removeNth (n := 1) 0 ![v, w]) = fun _ : Fin 1 => w := by
    funext i
    fin_cases i
    rfl
  have hremove1 : (Fin.removeNth (n := 1) 1 ![v, w]) = fun _ : Fin 1 => v := by
    funext i
    fin_cases i
    rfl
  rw [Fin.sum_univ_two] at hext
  rw [hremove0, hremove1] at hext
  norm_num at hext
  have heval (u q : E) :
      fderiv Real (fun y => rep y (fun _ : Fin 1 => q)) z u =
        fderiv Real omega z u q := by
    have hfun : (fun y => rep y (fun _ : Fin 1 => q)) = fun y => omega y q := by
      funext y
      simp [omega]
    have hvalue := homega.clm_apply (hasFDerivAt_const q z)
    rw [hfun, hvalue.fderiv, homega.fderiv]
    simp
  rw [heval v w, heval w v] at hext
  exact sub_eq_zero.mp hext

variable {EM : Type*} [NormedAddCommGroup EM] [NormedSpace Real EM]
  {HM : Type*} [TopologicalSpace HM]
  {IM : ModelWithCorners Real EM HM}
  {M : Type*} [TopologicalSpace M] [ChartedSpace HM M] [IsManifold IM ⊤ M]

private def oneFormLocalRep (alpha : DifferentialForm IM M 1) (x : M) :
    EM → EM [⋀^Fin 1]→L[Real] Real := fun z =>
  (trivializationAt (EM [⋀^Fin 1]→L[Real] Real)
    (Bundle.continuousAlternatingMap Real (Fin 1) EM (TangentSpace IM) Real
      (Bundle.Trivial M Real)) x
    ⟨(extChartAt IM x).symm z, alpha ((extChartAt IM x).symm z)⟩).2

private def oneFormLocalCoeff (alpha : DifferentialForm IM M 1) (x : M) :
    EM → EM →L[Real] Real := fun z =>
  (ofSubsingletonLIE (𝕜 := Real) (E := EM) (F := Real) (0 : Fin 1)).symm
    (oneFormLocalRep alpha x z)

private theorem oneFormLocalCoeff_contDiffOn
    (alpha : DifferentialForm IM M 1) (x : M) :
    ContDiffOn Real ∞ (oneFormLocalCoeff alpha x) (extChartAt IM x).target := by
  let L := (ofSubsingletonLIE (𝕜 := Real) (E := EM) (F := Real)
    (0 : Fin 1)).symm.toLinearIsometry.toContinuousLinearMap
  have hL : ContDiff Real ∞ L := L.contDiff
  exact hL.comp_contDiffOn ((localRep_contDiffOn alpha x).of_le (by simp))

private theorem oneFormLocalRep_extDeriv_eq_zero
    [BoundarylessManifold IM M] (alpha : DifferentialForm IM M 1)
    (x : M) {z : EM}
    (halpha : exteriorDerivative alpha ((extChartAt IM x).symm z) = 0)
    (hz : z ∈ (extChartAt IM x).target) :
    extDeriv (oneFormLocalRep alpha x) z = 0 := by
  let y := (extChartAt IM x).symm z
  have hy : y ∈ (extChartAt IM x).source := (extChartAt IM x).map_target hz
  have hloc := exteriorDerivative_localRepresentation (IM := IM) (M := M)
    (α := alpha) (x₀ := x) (x := y) hy
    (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := y))
  have hycoord : (extChartAt IM x) y = z := (extChartAt IM x).right_inv hz
  have hzero : exteriorDerivativeAt alpha y = 0 := by
    rw [← exteriorDerivative_apply]
    exact halpha
  have hzero' : exteriorDerivativeAtInterior alpha y
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := y)) = 0 := by
    exact hzero
  rw [hycoord] at hloc
  unfold oneFormLocalRep
  rw [← hloc, hzero']
  rw [continuousAlternatingMap_trivializationAt_apply]
  rfl

private theorem oneFormLocalCoeff_fderiv_symm
    [BoundarylessManifold IM M] (alpha : DifferentialForm IM M 1)
    (x : M) {z : EM}
    (halpha : exteriorDerivative alpha ((extChartAt IM x).symm z) = 0)
    (hz : z ∈ interior (extChartAt IM x).target) :
    ∀ v w : EM,
      fderiv Real (oneFormLocalCoeff alpha x) z v w =
        fderiv Real (oneFormLocalCoeff alpha x) z w v := by
  exact oneForm_fderiv_symm (oneFormLocalRep alpha x) z
    (((localRep_contDiffOn alpha x).contDiffAt
      (mem_interior_iff_mem_nhds.mp hz)).differentiableAt (by simp))
    (oneFormLocalRep_extDeriv_eq_zero alpha x halpha (interior_subset hz))

private theorem oneFormLocalCoeff_apply_mvfderiv_extChartAt
    (alpha : DifferentialForm IM M 1) (x : M) {y : M}
    (hy : y ∈ (extChartAt IM x).source) (v : TangentSpace IM y) :
    oneFormLocalCoeff alpha x (extChartAt IM x y)
        (mvfderiv (I := IM) (extChartAt IM x) y v) =
      alpha y (fun _ : Fin 1 => v) := by
  unfold oneFormLocalCoeff oneFormLocalRep
  rw [(extChartAt IM x).left_inv hy]
  let e := ofSubsingletonLIE (𝕜 := Real) (E := EM) (F := Real) (0 : Fin 1)
  let repY : EM [⋀^Fin 1]→L[Real] Real :=
    (trivializationAt (EM [⋀^Fin 1]→L[Real] Real)
    (Bundle.continuousAlternatingMap Real (Fin 1) EM (TangentSpace IM) Real
      (Bundle.Trivial M Real)) x ⟨y, alpha y⟩).2
  let q : EM := mvfderiv (I := IM) (extChartAt IM x) y v
  change (e (e.symm repY)) (fun _ : Fin 1 => q) = alpha y (fun _ : Fin 1 => v)
  rw [e.apply_symm_apply]
  dsimp only [repY]
  rw [continuousAlternatingMap_trivializationAt_apply]
  have hq : q =
      (trivializationAt EM (TangentSpace IM) x).continuousLinearMapAt Real y v := by
    dsimp only [q]
    unfold mvfderiv
    rw [← TangentBundle.continuousLinearMapAt_trivializationAt
      (by simpa [extChartAt_source] using hy)]
    rfl
  rw [hq]
  apply congrArg (alpha y)
  funext i
  exact Trivialization.symmL_continuousLinearMapAt
    (trivializationAt EM (TangentSpace IM) x)
    (by simpa [extChartAt_source] using hy) v

theorem exists_local_potential_of_exteriorDerivative_eq_zero_on
    [BoundarylessManifold IM M]
    (alpha : DifferentialForm IM M 1) (V : Set M) (hVopen : IsOpen V)
    (halpha : ∀ y ∈ V, exteriorDerivative alpha y = 0)
    {x : M} (hxV : x ∈ V) :
    ∃ U : Set M, ∃ f : M → Real,
      And (IsOpen U) (And (x ∈ U) (And (U ⊆ V) (And (f x = 0)
        (And (ContMDiffOn IM 𝓘(Real, Real) ∞ f U)
          (∀ y ∈ U, ∀ v : TangentSpace IM y,
            mvfderiv (I := IM) f y v = alpha y (fun _ : Fin 1 => v)))))) := by
  let z0 : EM := extChartAt IM x x
  have hz0int : z0 ∈ interior (extChartAt IM x).target :=
    (ModelWithCorners.isInteriorPoint_iff (I := IM)).mp
      (BoundarylessManifold.isInteriorPoint (I := IM) (M := M) (x := x))
  have hVcoord : (extChartAt IM x).symm ⁻¹' V ∈ nhds z0 := by
    apply (continuousAt_extChartAt_symm x).preimage_mem_nhds
    simpa only [z0, (extChartAt IM x).left_inv (mem_extChartAt_source x)] using
      hVopen.mem_nhds hxV
  have hcoord : Set.inter (interior (extChartAt IM x).target)
      ((extChartAt IM x).symm ⁻¹' V) ∈ nhds z0 :=
    inter_mem (isOpen_interior.mem_nhds hz0int) hVcoord
  obtain ⟨r, hr, hball⟩ := Metric.mem_nhds_iff.mp hcoord
  let B : Set EM := Metric.ball z0 r
  let omega := oneFormLocalCoeff alpha x
  let p : EM → Real := DifferentialGeometry.Analysis.Calculus.radialPotential omega z0
  let U : Set M := (extChartAt IM x).source ∩ (extChartAt IM x) ⁻¹' B
  let f : M → Real := p ∘ extChartAt IM x
  have hBopen : IsOpen B := Metric.isOpen_ball
  have hBsub : B ⊆ interior (extChartAt IM x).target := by
    intro z hz
    exact (hball (by simpa only [B] using hz)).1
  have hBsubV : ∀ z ∈ B, (extChartAt IM x).symm z ∈ V := by
    intro z hz
    exact (hball (by simpa only [B] using hz)).2
  have hsegmentB {z : EM} (hz : z ∈ B) (t : Real)
      (ht : t ∈ Set.Icc (0 : Real) 1) : z0 + t • (z - z0) ∈ B :=
    (convex_ball z0 r).add_smul_sub_mem (Metric.mem_ball_self hr) hz ht
  have hsegment {z : EM} (hz : z ∈ B) (t : Real) (ht : t ∈ Set.Icc (0 : Real) 1) :
      z0 + t • (z - z0) ∈ interior (extChartAt IM x).target := by
    apply hBsub
    exact hsegmentB hz t ht
  have hp (z : EM) (hz : z ∈ B) : HasFDerivAt p (omega z) z := by
    exact DifferentialGeometry.Analysis.Calculus.radialPotential_hasFDerivAt isOpen_interior
      (((oneFormLocalCoeff_contDiffOn alpha x).mono interior_subset).of_le (by simp))
      (fun t ht => hsegment hz t ht)
      (fun t ht v w => oneFormLocalCoeff_fderiv_symm alpha x
        (halpha _ (hBsubV _ (hsegmentB hz t ht))) (hsegment hz t ht) v w)
  have hpSmooth : ContDiffOn Real ∞ p B := by
    rw [contDiffOn_infty_iff_fderiv_of_isOpen hBopen]
    refine ⟨fun z hz => (hp z hz).differentiableAt.differentiableWithinAt, ?_⟩
    exact ((oneFormLocalCoeff_contDiffOn alpha x).mono
      (hBsub.trans interior_subset)).congr
      (fun z hz => by simpa only [omega] using (hp z hz).fderiv)
  refine ⟨U, f, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact isOpen_extChartAt_preimage' x hBopen
  · refine ⟨mem_extChartAt_source x, ?_⟩
    change extChartAt IM x x ∈ Metric.ball z0 r
    simpa only [z0] using Metric.mem_ball_self hr
  · intro y hy
    rw [← (extChartAt IM x).left_inv hy.1]
    exact hBsubV _ hy.2
  · simp [f, p, DifferentialGeometry.Analysis.Calculus.radialPotential, z0]
  · change ContMDiffOn IM 𝓘(Real, Real) ∞ (p ∘ extChartAt IM x) U
    exact (contMDiffOn_iff_contDiffOn.mpr hpSmooth).comp
      ((contMDiffOn_extChartAt (I := IM) (n := ∞) (x := x)).mono
        (fun y hy => by simpa only [U, extChartAt_source] using hy.1))
      (fun y hy => by simpa only [U] using hy.2)
  · intro y hy v
    have hysrc : y ∈ (extChartAt IM x).source := hy.1
    have hyB : extChartAt IM x y ∈ B := hy.2
    have hpAt := hp (extChartAt IM x y) hyB
    have hchart : MDifferentiableAt IM 𝓘(Real, EM) (extChartAt IM x) y :=
      mdifferentiableAt_extChartAt (by simpa [extChartAt_source] using hysrc)
    have hpM : MDifferentiableAt 𝓘(Real, EM) 𝓘(Real, Real) p (extChartAt IM x y) :=
      hpAt.hasMFDerivAt.mdifferentiableAt
    change mvfderiv (I := IM) (p ∘ extChartAt IM x) y v = _
    rw [mvfderiv_comp_apply y hpM hchart v]
    have hmodel :
        mvfderiv (I := 𝓘(Real, EM)) p (extChartAt IM x y)
            (mfderiv IM 𝓘(Real, EM) (extChartAt IM x) y v) =
          omega (extChartAt IM x y)
            (mvfderiv (I := IM) (extChartAt IM x) y v) := by
      unfold mvfderiv
      rw [mfderiv_eq_fderiv, hpAt.fderiv]
      rfl
    rw [hmodel]
    exact oneFormLocalCoeff_apply_mvfderiv_extChartAt alpha x hysrc v

theorem exists_local_potential [BoundarylessManifold IM M]
    (alpha : DifferentialForm IM M 1) (halpha : isClosed alpha) (x : M) :
    ∃ U : Set M, ∃ f : M → Real,
      And (IsOpen U) (And (x ∈ U) (And (f x = 0)
        (And (ContMDiffOn IM 𝓘(Real, Real) ∞ f U)
          (∀ y ∈ U, ∀ v : TangentSpace IM y,
            mvfderiv (I := IM) f y v = alpha y (fun _ : Fin 1 => v))))) := by
  obtain ⟨U, f, hUopen, hxU, hUsub, hfx, hf, hdf⟩ :=
    exists_local_potential_of_exteriorDerivative_eq_zero_on alpha Set.univ isOpen_univ
      (fun y hy => by
        rw [isClosed] at halpha
        simpa using congrArg (fun beta : DifferentialForm IM M 2 => beta y) halpha)
      (Set.mem_univ x)
  exact ⟨U, f, hUopen, hxU, hfx, hf, hdf⟩

end DifferentialForm
end DifferentialGeometry
