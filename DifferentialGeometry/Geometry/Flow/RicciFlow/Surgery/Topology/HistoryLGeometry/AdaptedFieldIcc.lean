import DifferentialGeometry.Geometry.Flow.RicciFlow.Surgery.Topology.HistoryLGeometry.FamilyChainSections

set_option autoImplicit false

noncomputable section

open scoped Bundle Manifold ContDiff Topology

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open Bundle Filter Set

open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Geometry.Riemannian.Geodesic
open DifferentialGeometry.Geometry.Riemannian.Variation
open DifferentialGeometry.Analysis.ODE.Flow
open DifferentialGeometry.Integral.Measure
open DifferentialGeometry.Integral.DivergenceTheorem
open DifferentialGeometry.Tensor0SBundle

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable {D : RealTimeInterval}

open private exists_parFrame adaptCoeff_smooth sumField_smooth from
DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.AdaptedField.Existence

omit [SigmaCompactSpace M] in
theorem exists_lAdaptedField_Icc
    (S : SolutionOn (I := I) (M := M) D) (hS : IsSolutionOn (I := I) S)
    (T : Real) (alpha : Real → M)
    (halpha : ContMDiff (modelWithCornersSelf Real Real) I ∞ alpha)
    {a a' b c : Real} (ha : a < a') (ha0 : 0 ≤ a') (hab : a' ≤ b)
    (hb : 0 < b) (hc : b < c)
    (hreg : ∀ s ∈ Set.Ioo a c, T - s ^ 2 ∈ D.regular)
    (V : TangentSpace I (alpha b)) :
    ∃ (P : ∀ s, TangentSpace I (alpha s)) (Omega' : Set Real),
      IsOpen Omega' ∧ Set.Icc a' b ⊆ Omega' ∧ Omega' ⊆ Set.Ioo a c ∧
      ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
        (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
            (alpha s) (P s) : TangentBundle I M)) Omega' ∧
      P b = V ∧
      IsLAdapted S T alpha P Omega' := by
  classical
  let q := S.base.metric (T - b ^ 2)
  obtain ⟨eps, heps, F, hFsmooth0, hFdiff0, hFpar0, hFON0⟩ :=
    exists_parFrame (E := E) q alpha halpha hb
  let rho : Real := min eps (min (a' - a) (c - b))
  let eta : Real := rho / 2
  have hrho : 0 < rho := by
    dsimp only [rho]
    exact lt_min heps (lt_min (sub_pos.mpr ha) (sub_pos.mpr hc))
  have heta : 0 < eta := by
    dsimp only [eta]
    linarith
  have heta_eps : eta < eps := by
    dsimp only [eta, rho]
    have hhalf : min eps (min (a' - a) (c - b)) / 2 <
        min eps (min (a' - a) (c - b)) := by linarith [hrho]
    exact hhalf.trans_le (min_le_left _ _)
  have heta_a : eta < a' - a := by
    dsimp only [eta, rho]
    have hhalf : min eps (min (a' - a) (c - b)) / 2 <
        min eps (min (a' - a) (c - b)) := by linarith [hrho]
    exact hhalf.trans_le (le_trans (min_le_right _ _) (min_le_left _ _))
  have heta_c : eta < c - b := by
    dsimp only [eta, rho]
    have hhalf : min eps (min (a' - a) (c - b)) / 2 <
        min eps (min (a' - a) (c - b)) := by linarith [hrho]
    exact hhalf.trans_le (le_trans (min_le_right _ _) (min_le_right _ _))
  let Omega' : Set Real := Set.Ioo (a' - eta) (b + eta)
  have hOmega : IsOpen Omega' := isOpen_Ioo
  have hIcc : Set.Icc a' b ⊆ Omega' := by
    intro s hs
    dsimp only [Omega']
    constructor <;> linarith [hs.1, hs.2, heta]
  have hOmegaRegularity : Omega' ⊆ Set.Ioo a c := by
    intro s hs
    dsimp only [Omega'] at hs
    constructor <;> linarith [hs.1, hs.2, heta_a, heta_c]
  have hOmegaFrame : Omega' ⊆ Set.Ioo (-eps) (b + eps) := by
    intro s hs
    dsimp only [Omega'] at hs
    constructor <;> linarith [hs.1, hs.2, heta_eps, ha0]
  have hFsmooth (i : Fin (Module.finrank Real E)) :=
    (hFsmooth0 i).mono hOmegaFrame
  have hFdiff (i : Fin (Module.finrank Real E)) (s : Real) (hs : s ∈ Omega') :=
    hFdiff0 i s (hOmegaFrame hs)
  have hFON (s : Real) (hs : s ∈ Omega') (i j : Fin (Module.finrank Real E)) :=
    hFON0 s (hOmegaFrame hs) i j
  let aij : Real → Fin (Module.finrank Real E) → Fin (Module.finrank Real E) → Real :=
    fun s i j ↦ q.inner (alpha s) (F i s)
      ((-2 * s) •
          ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (F j s) -
        covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha (F j) s)
  have haij (i j : Fin (Module.finrank Real E)) :
      ContDiffOn Real ∞ (fun s ↦ aij s i j) Omega' := by
    simpa only [aij] using adaptCoeff_smooth (E := E) S hS T q alpha
      (F i) (F j) halpha hOmega (hFsmooth i) (hFsmooth j)
      (fun s hs ↦ hreg s (hOmegaRegularity hs))
  let amat : Real → Matrix (Fin (Module.finrank Real E))
      (Fin (Module.finrank Real E)) Real := fun s i j ↦ aij s i j
  let A : Unit → Real →
      ((Fin (Module.finrank Real E) → Real) →L[Real]
        (Fin (Module.finrank Real E) → Real)) := fun _ s ↦
    (Matrix.toLin' (amat s)).toContinuousLinearMap
  have hA : ContDiffOn Real ∞ (Function.uncurry A)
      (Set.univ ×ˢ Omega') := by
    rw [contDiffOn_clm_apply]
    intro z
    rw [contDiffOn_pi]
    intro i
    change ContDiffOn Real ∞
      (fun p : Unit × Real ↦ ∑ j, aij p.2 i j * z j) (Set.univ ×ˢ Omega')
    exact ContDiffOn.sum fun j _ ↦
      ((haij i j).comp contDiffOn_snd (fun p hp ↦ hp.2)).mul contDiffOn_const
  have hbmem : b ∈ Set.Ioo (a' - eta) (b + eta) := by
    constructor <;> linarith [hb, heta, hab]
  let z0 : Unit → (Fin (Module.finrank Real E) → Real) := fun _ i ↦
    q.inner (alpha b) (F i b) V
  have hz0 : ContDiffOn Real ∞ z0 Set.univ := contDiffOn_const
  have hA' : ContDiffOn Real ∞ (Function.uncurry A)
      (Set.univ ×ˢ Set.Ioo (a' - eta) (b + eta)) := by
    simpa only [Omega'] using hA
  let z : Real → (Fin (Module.finrank Real E) → Real) := fun s ↦
    linearODESolution A (a' - eta) (b + eta) b z0 () s
  have hzRaw := linearODESolution_contDiffOn_top hbmem isOpen_univ hA' hz0
  have hz : ContDiffOn Real ∞ z Omega' := by
    have hpair : ContDiff Real ∞ (fun s : Real ↦ ((), s)) :=
      contDiff_const.prodMk contDiff_id
    have hcomp := hzRaw.comp hpair.contDiffOn
      (fun s hs ↦ ⟨Set.mem_univ (), by simpa only [Omega'] using hs⟩)
    change ContDiffOn Real ∞
      (fun s ↦ linearODESolution A (a' - eta) (b + eta) b z0 () s) Omega' at hcomp
    exact hcomp
  let P : ∀ s, TangentSpace I (alpha s) := fun s ↦
    ∑ i : Fin (Module.finrank Real E), z s i • F i s
  have hPsmooth : ContMDiffOn (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real ↦
          (TotalSpace.mk' E (E := (TangentSpace I : M → Type _))
          (alpha s) (P s) : TangentBundle I M)) Omega' := by
    simpa only [P] using
      sumField_smooth (E := E) alpha z F halpha hOmega hz hFsmooth
  have hzb : z b = z0 () := by
    exact linearODESolution_initial A (a' - eta) (b + eta) b z0 ()
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I (alpha b)) := by
    rw [Fintype.card_fin]
    rfl
  have hPb : P b = V := by
    dsimp only [P]
    rw [hzb]
    dsimp only [z0]
    exact (Geometry.Riemannian.expand_orthonormal q (alpha b) hcard
      (fun i ↦ F i b) (hFON b (hIcc ⟨hab, le_rfl⟩)) V).symm
  refine ⟨P, Omega', hOmega, hIcc, hOmegaRegularity, hPsmooth, hPb, ?_⟩
  intro s hs
  change covDerivAlong (I := I) (S.base.metric (T - s ^ 2)) alpha P s =
    (-2 * s) •
      ricciSharp (I := I) (S.base.metric (T - s ^ 2)) (alpha s) (P s)
  let g := S.base.metric (T - s ^ 2)
  have hsIoo : s ∈ Set.Ioo (a' - eta) (b + eta) := by
    simpa only [Omega'] using hs
  have hzDeriv : HasDerivAt z (A () s (z s)) s := by
    simpa only [z] using linearODESolution_hasDerivAt hbmem
      hA'.continuousOn (Set.mem_univ ()) hsIoo
  have hziDiff (i : Fin (Module.finrank Real E)) :
      DifferentiableAt Real (fun r ↦ z r i) s :=
    ((((contDiffOn_pi.mp hz) i).differentiableOn (by simp)) s hs).differentiableAt
      (hOmega.mem_nhds hs)
  have hziDeriv (i : Fin (Module.finrank Real E)) :
      deriv (fun r ↦ z r i) s = (A () s (z s)) i := by
    exact ((hasDerivAt_pi.mp hzDeriv) i).deriv
  have htermDiff (i : Fin (Module.finrank Real E)) : DifferentiableAt Real
      (chartRepAt (I := I) alpha (fun r ↦ z r i • F i r) s) s := by
    rw [chartRepAt_smulFun]
    exact (hziDiff i).smul (hFdiff i s hs)
  have hAapply (i : Fin (Module.finrank Real E)) :
      (A () s (z s)) i = ∑ j, aij s i j * z s j := by
    rfl
  have hDP : covDerivAlong (I := I) g alpha P s =
      ∑ i : Fin (Module.finrank Real E), (
        (∑ j, aij s i j * z s j) • F i s +
          z s i • covDerivAlong (I := I) g alpha (F i) s) := by
    dsimp only [P]
    rw [covDerivAlong_sum (I := I) g alpha Finset.univ
      (fun i r ↦ z r i • F i r) s (fun i _ ↦ htermDiff i)]
    refine Finset.sum_congr rfl fun i _ ↦ ?_
    rw [covDerivAlong_smulFun (I := I) g alpha (fun r ↦ z r i) (F i) s
      (hziDiff i) (hFdiff i s hs), hziDeriv i, hAapply i]
  let B : Fin (Module.finrank Real E) → TangentSpace I (alpha s) := fun j ↦
    (-2 * s) • ricciSharp (I := I) g (alpha s) (F j s) -
      covDerivAlong (I := I) g alpha (F j) s
  have hcard_s : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I (alpha s)) := by
    rw [Fintype.card_fin]
    rfl
  have hBexp (j : Fin (Module.finrank Real E)) :
      B j = ∑ i, aij s i j • F i s := by
    have hexp := Geometry.Riemannian.expand_orthonormal q (alpha s) hcard_s
      (fun i ↦ F i s) (hFON s hs) (B j)
    rw [hexp]
  have hswap :
      (∑ i : Fin (Module.finrank Real E),
        (∑ j, aij s i j * z s j) • F i s) =
      ∑ j : Fin (Module.finrank Real E), z s j •
        (∑ i, aij s i j • F i s) := by
    simp_rw [Finset.sum_smul, Finset.smul_sum, mul_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ ↦ Finset.sum_congr rfl fun j _ ↦ ?_
    module
  rw [hDP, Finset.sum_add_distrib, hswap]
  have hcols : (∑ j : Fin (Module.finrank Real E), z s j •
      (∑ i, aij s i j • F i s)) = ∑ j, z s j • B j := by
    refine Finset.sum_congr rfl fun j _ ↦ ?_
    rw [← hBexp j]
  rw [hcols]
  dsimp only [B, g]
  dsimp only [P]
  simp_rw [smul_sub]
  rw [Finset.sum_sub_distrib, sub_add_cancel]
  rw [map_sum]
  simp_rw [map_smul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [mul_comm]

end DifferentialGeometry.PDE.RicciFlow.Perelman
