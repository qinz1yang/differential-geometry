import DifferentialGeometry.Geometry.Exponential.IntrinsicJacobiJets

import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.CovariantDerivativeTower
import DifferentialGeometry.Geometry.Compactness.CheegerGromov.Pointed.EMetric

set_option autoImplicit false

noncomputable section

open Bundle
open DifferentialGeometry.Geometry.Riemannian
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.Exponential
open DifferentialGeometry.Geometry.Riemannian.Variation
open scoped Bundle Manifold ContDiff ENNReal Topology

namespace DifferentialGeometry
namespace HCGCompactness

inductive IntrJetAtom
  | pathT
  | pathDt
  | aJet (n : Nat)
  | aTime (n : Nat)
  | bJet (n : Nat)
  | bTime (n : Nat)

inductive CurvJetTerm
  | zero
  | atom (a : IntrJetAtom)
  | add (x y : CurvJetTerm)
  | scale (c : Real) (x : CurvJetTerm)
  | curv (k : Nat) (slots : Fin (k + 3) -> CurvJetTerm)

instance : Zero CurvJetTerm := ⟨CurvJetTerm.zero⟩
instance : Add CurvJetTerm := ⟨CurvJetTerm.add⟩
instance : SMul Real CurvJetTerm := ⟨CurvJetTerm.scale⟩

private def slots3 (x y z : CurvJetTerm) : Fin 3 -> CurvJetTerm :=
  Fin.cons x (Fin.cons y (fun _ => z))

private def slots4 (w x y z : CurvJetTerm) : Fin 4 -> CurvJetTerm :=
  Fin.cons w (slots3 x y z)

def intrCorrTerm (n : Nat) : CurvJetTerm :=
  let T := CurvJetTerm.atom IntrJetAtom.pathT
  let dT := CurvJetTerm.atom IntrJetAtom.pathDt
  let A := CurvJetTerm.atom (IntrJetAtom.aJet 0)
  let dA := CurvJetTerm.atom (IntrJetAtom.aTime 0)
  let B := CurvJetTerm.atom (IntrJetAtom.bJet n)
  let dB := CurvJetTerm.atom (IntrJetAtom.bTime n)
  CurvJetTerm.curv 1 (slots4 T A T B) +
    CurvJetTerm.curv 0 (slots3 dA T B) +
    CurvJetTerm.curv 0 (slots3 A dT B) +
    (2 : Real) • CurvJetTerm.curv 0 (slots3 A T dB) +
    CurvJetTerm.curv 1 (slots4 A B T T) +
    CurvJetTerm.curv 0 (slots3 B dA T) +
    CurvJetTerm.curv 0 (slots3 B T dA)

def CurvJetTerm.finSum : {n : Nat} -> (Fin n -> CurvJetTerm) -> CurvJetTerm
  | 0, _ => 0
  | _ + 1, terms =>
      terms 0 + CurvJetTerm.finSum (fun i => terms i.succ)

def CurvJetTerm.launchDeriv : CurvJetTerm -> CurvJetTerm
  | .zero => 0
  | .atom .pathT => .atom (.aTime 0)
  | .atom .pathDt => 0
  | .atom (.aJet n) => .atom (.aJet (n + 1))
  | .atom (.aTime n) =>
      .atom (.aTime (n + 1)) +
        .curv 0 (slots3 (.atom (.aJet 0)) (.atom .pathT)
          (.atom (.aJet n)))
  | .atom (.bJet n) => .atom (.bJet (n + 1))
  | .atom (.bTime n) =>
      .atom (.bTime (n + 1)) +
        .curv 0 (slots3 (.atom (.aJet 0)) (.atom .pathT)
          (.atom (.bJet n)))
  | .add x y => x.launchDeriv + y.launchDeriv
  | .scale c x => c • x.launchDeriv
  | .curv k slots =>
      .curv (k + 1) (Fin.cons (.atom (.aJet 0)) slots) +
        CurvJetTerm.finSum (fun i =>
          .curv k (Function.update slots i (slots i).launchDeriv))

def CurvJetTerm.launchIter : Nat -> CurvJetTerm -> CurvJetTerm
  | 0, term => term
  | n + 1, term => (term.launchIter n).launchDeriv

def intrResidualTerm : Nat -> CurvJetTerm
  | 0 => 0
  | n + 1 =>
      (intrResidualTerm n).launchDeriv +
        (-1 : Real) • intrCorrTerm n

def CurvJetTerm.majorant
    (C : Nat -> Real) (B : IntrJetAtom -> Real) : CurvJetTerm -> Real
  | .zero => 0
  | .atom leaf => B leaf
  | .add x y => x.majorant C B + y.majorant C B
  | .scale c x => |c| * x.majorant C B
  | .curv k slots => C k * ∏ i, (slots i).majorant C B

theorem CurvJetTerm.majorant_nonneg
    (C : Nat -> Real) (B : IntrJetAtom -> Real)
    (hC : forall k, 0 <= C k) (hB : forall atom, 0 <= B atom) :
    forall term : CurvJetTerm, 0 <= term.majorant C B := by
  intro term
  induction term with
  | zero =>
      exact le_rfl
  | atom leaf =>
      exact hB leaf
  | add x y ihx ihy =>
      exact add_nonneg ihx ihy
  | scale c x ih =>
      exact mul_nonneg (abs_nonneg c) ih
  | curv k slots ih =>
      exact mul_nonneg (hC k) (Finset.prod_nonneg fun i _ => ih i)

def CurvJetTerm.AllAtoms : CurvJetTerm -> (IntrJetAtom -> Prop) -> Prop
  | CurvJetTerm.zero, _ => True
  | CurvJetTerm.atom leaf, P => P leaf
  | CurvJetTerm.add x y, P => x.AllAtoms P ∧ y.AllAtoms P
  | CurvJetTerm.scale _ x, P => x.AllAtoms P
  | CurvJetTerm.curv _ slots, P => forall i, (slots i).AllAtoms P

def IntrJetAtom.AtMost : IntrJetAtom -> Nat -> Prop
  | .pathT, _ => True
  | .pathDt, _ => True
  | .aJet k, n => k <= n
  | .aTime k, n => k <= n
  | .bJet k, n => k <= n
  | .bTime k, n => k <= n

theorem IntrJetAtom.atMost_mono
    {atom : IntrJetAtom} {m n : Nat} (hmn : m <= n) :
    atom.AtMost m -> atom.AtMost n := by
  cases atom with
  | pathT =>
      intro h
      trivial
  | pathDt =>
      intro h
      trivial
  | aJet k =>
      intro hk
      exact hk.trans hmn
  | aTime k =>
      intro hk
      exact hk.trans hmn
  | bJet k =>
      intro hk
      exact hk.trans hmn
  | bTime k =>
      intro hk
      exact hk.trans hmn

theorem CurvJetTerm.allAtoms_mono
    {P Q : IntrJetAtom -> Prop}
    (hPQ : forall atom, P atom -> Q atom) :
    forall term : CurvJetTerm, term.AllAtoms P -> term.AllAtoms Q := by
  intro term
  induction term with
  | zero =>
      intro hterm
      trivial
  | atom leaf =>
      intro hterm
      exact hPQ leaf hterm
  | add x y ihx ihy =>
      intro hterm
      exact ⟨ihx hterm.1, ihy hterm.2⟩
  | scale c x ih =>
      intro hterm
      exact ih hterm
  | curv k slots ih =>
      intro hterm i
      exact ih i (hterm i)

theorem CurvJetTerm.finSum_atoms
    {P : IntrJetAtom -> Prop} :
    forall {n : Nat} (terms : Fin n -> CurvJetTerm),
      (forall i, (terms i).AllAtoms P) ->
        (CurvJetTerm.finSum terms).AllAtoms P := by
  intro n
  induction n with
  | zero =>
      intro terms hterms
      trivial
  | succ n ih =>
      intro terms hterms
      exact ⟨hterms 0, ih (fun i => terms i.succ) (fun i => hterms i.succ)⟩

theorem CurvJetTerm.launch_atoms :
    forall (term : CurvJetTerm) (n : Nat),
      term.AllAtoms (fun atom => atom.AtMost n) ->
        term.launchDeriv.AllAtoms (fun atom => atom.AtMost (n + 1)) := by
  intro term
  induction term with
  | zero =>
      intro n hterm
      trivial
  | atom leaf =>
      intro n hterm
      cases leaf with
      | pathT =>
          exact Nat.zero_le _
      | pathDt =>
          trivial
      | aJet k =>
          exact Nat.add_le_add_right hterm 1
      | aTime k =>
          constructor
          · exact Nat.add_le_add_right hterm 1
          · intro i
            fin_cases i
            · exact Nat.zero_le _
            · trivial
            · exact hterm.trans (Nat.le_succ n)
      | bJet k =>
          exact Nat.add_le_add_right hterm 1
      | bTime k =>
          constructor
          · exact Nat.add_le_add_right hterm 1
          · intro i
            fin_cases i
            · exact Nat.zero_le _
            · trivial
            · exact hterm.trans (Nat.le_succ n)
  | add x y ihx ihy =>
      intro n hterm
      exact ⟨ihx n hterm.1, ihy n hterm.2⟩
  | scale c x ih =>
      intro n hterm
      exact ih n hterm
  | curv k slots ih =>
      intro n hterm
      constructor
      · intro i
        refine Fin.cases ?_ (fun j => ?_) i
        · exact Nat.zero_le _
        · exact CurvJetTerm.allAtoms_mono
            (fun atom hatom =>
              IntrJetAtom.atMost_mono (Nat.le_succ n) hatom)
            (slots j) (hterm j)
      · apply CurvJetTerm.finSum_atoms
        intro i j
        by_cases hji : j = i
        · subst j
          rw [Function.update_self]
          exact ih i n (hterm i)
        · rw [Function.update_of_ne hji]
          exact CurvJetTerm.allAtoms_mono
            (fun atom hatom =>
              IntrJetAtom.atMost_mono (Nat.le_succ n) hatom)
            (slots j) (hterm j)

private theorem slots3_atoms
    {P : IntrJetAtom -> Prop} {x y z : CurvJetTerm}
    (hx : x.AllAtoms P) (hy : y.AllAtoms P) (hz : z.AllAtoms P) :
    forall i, (slots3 x y z i).AllAtoms P := by
  intro i
  fin_cases i
  · exact hx
  · exact hy
  · exact hz

private theorem slots4_atoms
    {P : IntrJetAtom -> Prop} {w x y z : CurvJetTerm}
    (hw : w.AllAtoms P) (hx : x.AllAtoms P)
    (hy : y.AllAtoms P) (hz : z.AllAtoms P) :
    forall i, (slots4 w x y z i).AllAtoms P := by
  intro i
  fin_cases i
  · exact hw
  · exact hx
  · exact hy
  · exact hz

theorem intrCorrTerm_atoms (n : Nat) :
    (intrCorrTerm n).AllAtoms (fun atom => atom.AtMost n) := by
  let P : IntrJetAtom -> Prop := fun atom => atom.AtMost n
  let T := CurvJetTerm.atom IntrJetAtom.pathT
  let dT := CurvJetTerm.atom IntrJetAtom.pathDt
  let A := CurvJetTerm.atom (IntrJetAtom.aJet 0)
  let dA := CurvJetTerm.atom (IntrJetAtom.aTime 0)
  let B := CurvJetTerm.atom (IntrJetAtom.bJet n)
  let dB := CurvJetTerm.atom (IntrJetAtom.bTime n)
  have hT : T.AllAtoms P := trivial
  have hdT : dT.AllAtoms P := trivial
  have hA : A.AllAtoms P := Nat.zero_le n
  have hdA : dA.AllAtoms P := Nat.zero_le n
  have hB : B.AllAtoms P := le_rfl
  have hdB : dB.AllAtoms P := le_rfl
  have h1 := slots4_atoms hT hA hT hB
  have h2 := slots3_atoms hdA hT hB
  have h3 := slots3_atoms hA hdT hB
  have h4 := slots3_atoms hA hT hdB
  have h5 := slots4_atoms hA hB hT hT
  have h6 := slots3_atoms hB hdA hT
  have h7 := slots3_atoms hB hT hdA
  exact ⟨⟨⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩, h6⟩, h7⟩

theorem intrResidual_atoms :
    forall n : Nat,
      (intrResidualTerm (n + 1)).AllAtoms
        (fun atom => atom.AtMost n) := by
  intro n
  induction n with
  | zero =>
      change
        ((intrResidualTerm 0).launchDeriv +
          (-1 : Real) • intrCorrTerm 0).AllAtoms
            (fun atom => atom.AtMost 0)
      exact ⟨trivial, intrCorrTerm_atoms 0⟩
  | succ n ih =>
      change
        ((intrResidualTerm (n + 1)).launchDeriv +
          (-1 : Real) • intrCorrTerm (n + 1)).AllAtoms
            (fun atom => atom.AtMost (n + 1))
      exact
        ⟨CurvJetTerm.launch_atoms (intrResidualTerm (n + 1)) n ih,
          intrCorrTerm_atoms (n + 1)⟩

theorem CurvJetTerm.allAtoms_true :
    forall term : CurvJetTerm, term.AllAtoms (fun _ => True) := by
  intro term
  induction term with
  | zero => trivial
  | atom leaf => trivial
  | add x y ihx ihy => exact ⟨ihx, ihy⟩
  | scale c x ih => exact ih
  | curv k slots ih => exact ih

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E]
  [InnerProductSpace Real E] [FiniteDimensional Real E] [CompleteSpace E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [SigmaCompactSpace M]
variable [RiemannianBundle (fun x : M => TangentSpace I x)]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def IntrJetAtom.eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (atom : IntrJetAtom) (q : Real × Real) :
    TangentSpace I
      (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)) :=
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let A : forall r t : Real, TangentSpace I (f r t) := fun r t =>
    varFst (I := I) f r t
  let B : forall r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  match atom with
  | .pathT => varSnd (I := I) f q.1 q.2
  | .pathDt =>
      covSnd (I := I) g f (fun r t => varSnd (I := I) f r t) q.1 q.2
  | .aJet n => covFstIter (I := I) g f n A q.1 q.2
  | .aTime n =>
      covSnd (I := I) g f
        (fun r t => covFstIter (I := I) g f n A r t) q.1 q.2
  | .bJet n => covFstIter (I := I) g f n B q.1 q.2
  | .bTime n =>
      covSnd (I := I) g f
        (fun r t => covFstIter (I := I) g f n B r t) q.1 q.2

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.pathDt_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r t : Real) :
    IntrJetAtom.pathDt.eval (I := I) g hEnorm p u a b (r, t) = 0 := by
  let f : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  let gamma : Real -> M := fun v => f r v
  have hgamma :
      ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    have hincl :
        ContMDiff
          (modelWithCornersSelf Real Real)
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun v : Real => ((r, (0 : Real)), v)) :=
      (contMDiff_const.prodMk contMDiff_const).prodMk contMDiff_id
    simpa only [gamma, f, Function.comp_apply] using
      (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hgeo :
      DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
        (I := I) g gamma := by
    simpa only [gamma, f, intrLaunch3, zero_smul, add_zero] using
      intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
        (show TangentSpace I p from u + r • a)
  have hz :=
    (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
      (I := I) g gamma t hgamma).2 (hgeo.hasGeodesicEquationAt t)
  simpa only [IntrJetAtom.eval, f, gamma, covSnd, varSnd] using hz

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.aJet_eq_self
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r t : Real) :
    (IntrJetAtom.aJet n).eval (I := I) g hEnorm p u a b (r, t) =
      (IntrJetAtom.bJet n).eval (I := I) g hEnorm p u a a (r, t) := by
  let fb : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  let fa : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a a ((s, 0), v)
  have hf : fb = fa := by
    funext s v
    simp only [fb, fa, intrLaunch3, zero_smul, add_zero]
  change
    covFstIter (I := I) g fb n
        (fun s v => varFst (I := I) fb s v) r t =
      intrLaunchJet (I := I) g hEnorm p u a a n (r, t)
  rw [hf]
  exact intrAJet_self (I := I) g hEnorm p u a n (r, t)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.aTime_eq_self
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r t : Real) :
    (IntrJetAtom.aTime n).eval (I := I) g hEnorm p u a b (r, t) =
      (IntrJetAtom.bTime n).eval (I := I) g hEnorm p u a a (r, t) := by
  let fb : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  let fa : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a a ((s, 0), v)
  have hf : fb = fa := by
    funext s v
    simp only [fb, fa, intrLaunch3, zero_smul, add_zero]
  change
    covSnd (I := I) g fb
        (fun s v =>
          covFstIter (I := I) g fb n
            (fun x y => varFst (I := I) fb x y) s v) r t =
      covSnd (I := I) g fa
        (fun s v =>
          intrLaunchJet (I := I) g hEnorm p u a a n (s, v)) r t
  rw [hf]
  congr 1
  funext s v
  exact intrAJet_self (I := I) g hEnorm p u a n (s, v)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.aJet_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r : Real) :
    (IntrJetAtom.aJet n).eval (I := I) g hEnorm p u a b (r, 0) = 0 := by
  let f : Real -> Real -> M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
  let A : forall s t : Real, TangentSpace I (f s t) := fun s t =>
    varFst (I := I) f s t
  change covFstIter (I := I) g f n A r 0 = 0
  have hzero : forall s, A s 0 = 0 := by
    intro s
    change varFst (I := I) f s 0 = 0
    unfold varFst
    have hconst : (fun x : Real => f x 0) = fun _ : Real => p := by
      funext x
      exact intrinsicGeodesic_zero (I := I) g hEnorm p _
    rw [hconst, mfderiv_const]
    rfl
  exact covFstIter_zero_of (I := I) g f A 0 hzero n r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.bJet_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r : Real) :
    (IntrJetAtom.bJet n).eval (I := I) g hEnorm p u a b (r, 0) = 0 := by
  change intrLaunchJet (I := I) g hEnorm p u a b n (r, 0) = 0
  exact intrLaunchJet_time0 (I := I) g hEnorm p u a b n r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
noncomputable def CurvJetTerm.eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    CurvJetTerm -> forall q : Real × Real,
      TangentSpace I
        (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
  | .zero, _ => 0
  | .atom x, q => x.eval (I := I) g hEnorm p u a b q
  | .add x y, q =>
      x.eval g hEnorm p u a b q +
        y.eval g hEnorm p u a b q
  | .scale c x, q => c • x.eval g hEnorm p u a b q
  | .curv k slots, q =>
      curvOpN (I := I) g k
        (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
        (fun i => (slots i).eval g hEnorm p u a b q)

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem CurvJetTerm.eval_le_at
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E)
    (C : Nat -> Real) (hC : forall k, 0 <= C k)
    (B : IntrJetAtom -> Real) (P : IntrJetAtom -> Prop)
    (hcurv : forall (k : Nat) (x : M)
      (v : Fin (k + 3) -> TangentSpace I x),
      Real.sqrt
          (g.inner x (curvOpN (I := I) g k x v)
            (curvOpN (I := I) g k x v)) <=
        C k * ∏ i, Real.sqrt (g.inner x (v i) (v i)))
    (q : Real × Real)
    (hatom : forall (atom : IntrJetAtom), P atom ->
        Real.sqrt
            (g.inner
              (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
              (atom.eval (I := I) g hEnorm p u a b q)
              (atom.eval (I := I) g hEnorm p u a b q)) <=
          B atom) :
    forall term : CurvJetTerm, term.AllAtoms P ->
        Real.sqrt
            (g.inner
              (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
              (term.eval (I := I) g hEnorm p u a b q)
              (term.eval (I := I) g hEnorm p u a b q)) <=
          term.majorant C B := by
  intro term
  induction term with
  | zero =>
      intro hterm
      simp only [CurvJetTerm.eval, CurvJetTerm.majorant, map_zero,
        Real.sqrt_zero]
      exact le_rfl
  | atom atom =>
      intro hterm
      exact hatom atom hterm
  | add y z ihy ihz =>
      intro hterm
      let x :=
        intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)
      calc
        Real.sqrt
            (g.inner x
              ((y + z).eval (I := I) g hEnorm p u a b q)
              ((y + z).eval (I := I) g hEnorm p u a b q)) <=
            Real.sqrt
                (g.inner x
                  (y.eval (I := I) g hEnorm p u a b q)
                  (y.eval (I := I) g hEnorm p u a b q)) +
              Real.sqrt
                (g.inner x
                  (z.eval (I := I) g hEnorm p u a b q)
                  (z.eval (I := I) g hEnorm p u a b q)) := by
          simpa only [CurvJetTerm.eval] using
            Geometry.Riemannian.sqrt_inner_add_le (I := I) g x
              (y.eval (I := I) g hEnorm p u a b q)
              (z.eval (I := I) g hEnorm p u a b q)
        _ <= y.majorant C B + z.majorant C B :=
          add_le_add (ihy hterm.1) (ihz hterm.2)
        _ = (y + z).majorant C B := rfl
  | scale c y ih =>
      intro hterm
      let x :=
        intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)
      calc
        Real.sqrt
            (g.inner x
              ((c • y).eval (I := I) g hEnorm p u a b q)
              ((c • y).eval (I := I) g hEnorm p u a b q)) =
            |c| * Real.sqrt
              (g.inner x
                (y.eval (I := I) g hEnorm p u a b q)
                (y.eval (I := I) g hEnorm p u a b q)) := by
          simpa only [CurvJetTerm.eval] using
            Geometry.Riemannian.sqrt_inner_smul (I := I) g x c
              (y.eval (I := I) g hEnorm p u a b q)
        _ <= |c| * y.majorant C B :=
          mul_le_mul_of_nonneg_left (ih hterm) (abs_nonneg c)
        _ = (c • y).majorant C B := rfl
  | curv k slots ih =>
      intro hterm
      let x :=
        intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2)
      have hprod :
          (∏ i : Fin (k + 3),
              Real.sqrt
                (g.inner x
                  ((slots i).eval (I := I) g hEnorm p u a b q)
                  ((slots i).eval (I := I) g hEnorm p u a b q))) <=
            ∏ i : Fin (k + 3), (slots i).majorant C B := by
        apply Finset.prod_le_prod
        · intro i hi
          exact Real.sqrt_nonneg _
        · intro i hi
          exact ih i (hterm i)
      calc
        Real.sqrt
            (g.inner x
              ((CurvJetTerm.curv k slots).eval
                (I := I) g hEnorm p u a b q)
              ((CurvJetTerm.curv k slots).eval
                (I := I) g hEnorm p u a b q)) <=
            C k * ∏ i : Fin (k + 3),
              Real.sqrt
                (g.inner x
                  ((slots i).eval (I := I) g hEnorm p u a b q)
                  ((slots i).eval (I := I) g hEnorm p u a b q)) := by
          simpa only [CurvJetTerm.eval] using
            hcurv k x
              (fun i => (slots i).eval (I := I) g hEnorm p u a b q)
        _ <= C k * ∏ i : Fin (k + 3), (slots i).majorant C B :=
          mul_le_mul_of_nonneg_left hprod (hC k)
        _ = (CurvJetTerm.curv k slots).majorant C B := rfl

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem CurvJetTerm.eval_le_atoms
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E)
    (C : Nat -> Real) (hC : forall k, 0 <= C k)
    (B : IntrJetAtom -> Real) (P : IntrJetAtom -> Prop)
    (hcurv : forall (k : Nat) (x : M)
      (v : Fin (k + 3) -> TangentSpace I x),
      Real.sqrt
          (g.inner x (curvOpN (I := I) g k x v)
            (curvOpN (I := I) g k x v)) <=
        C k * ∏ i, Real.sqrt (g.inner x (v i) (v i)))
    (hatom : forall (atom : IntrJetAtom), P atom ->
      forall q : Real × Real,
        Real.sqrt
            (g.inner
              (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
              (atom.eval (I := I) g hEnorm p u a b q)
              (atom.eval (I := I) g hEnorm p u a b q)) <=
          B atom) :
    forall term : CurvJetTerm, term.AllAtoms P ->
      forall q : Real × Real,
        Real.sqrt
            (g.inner
              (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
              (term.eval (I := I) g hEnorm p u a b q)
              (term.eval (I := I) g hEnorm p u a b q)) <=
          term.majorant C B := by
  intro term hterm q
  exact CurvJetTerm.eval_le_at
    (I := I) g hEnorm p u a b C hC B P hcurv q
    (fun atom hatomP => hatom atom hatomP q) term hterm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem CurvJetTerm.eval_le_of
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E)
    (C : Nat -> Real) (hC : forall k, 0 <= C k)
    (B : IntrJetAtom -> Real)
    (hcurv : forall (k : Nat) (x : M)
      (v : Fin (k + 3) -> TangentSpace I x),
      Real.sqrt
          (g.inner x (curvOpN (I := I) g k x v)
            (curvOpN (I := I) g k x v)) <=
        C k * ∏ i, Real.sqrt (g.inner x (v i) (v i)))
    (hatom : forall (atom : IntrJetAtom) (q : Real × Real),
      Real.sqrt
          (g.inner
            (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
            (atom.eval (I := I) g hEnorm p u a b q)
            (atom.eval (I := I) g hEnorm p u a b q)) <=
        B atom) :
    forall (term : CurvJetTerm) (q : Real × Real),
      Real.sqrt
          (g.inner
            (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
            (term.eval (I := I) g hEnorm p u a b q)
            (term.eval (I := I) g hEnorm p u a b q)) <=
        term.majorant C B := by
  intro term q
  exact CurvJetTerm.eval_le_atoms
    (I := I) g hEnorm p u a b C hC B (fun _ => True)
    hcurv (fun atom _ q => hatom atom q)
    term (CurvJetTerm.allAtoms_true term) q

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem CurvJetTerm.eval_le_geom
    (P : PointedRiemannianManifold.{u, uE, uH} (I := I))
    (hcomplete : MetricComplete (I := I) P)
    (hP : BoundedGeometry (I := I) P)
    (p : P.M) (u a b : E) (B : IntrJetAtom -> Real) :
    letI : TopologicalSpace P.M := P.topology
    letI : ChartedSpace H P.M := P.charted
    letI : IsManifold I ∞ P.M := P.smooth
    letI : SigmaCompactSpace P.M := P.sigmaCompact
    letI : T2Space P.M := P.t2
    letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
    letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
      P.riemBundle (I := I)
    letI : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
      P.riemInner (I := I)
    letI : IsContinuousRiemannianBundle E
        (fun x : P.M => TangentSpace I x) :=
      P.riemBundle_cont (I := I)
    letI : EMetricSpace P.M := P.emetricSpace (I := I)
    letI : CompleteSpace P.M :=
      MetricComplete.complete (I := I) P hcomplete
    let hEnorm : forall (x : P.M) (v : TangentSpace I x),
        ‖v‖ₑ = ENNReal.ofReal
          (Real.sqrt (P.metric.inner x v v)) := by
      intro x v
      simpa using
        (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
          (I := I) P.metric x v)
    (forall (atom : IntrJetAtom) (q : Real × Real),
      Real.sqrt
          (P.metric.inner
            (intrLaunch3 (I := I) P.metric hEnorm p u a b
              ((q.1, 0), q.2))
            (atom.eval (I := I) P.metric hEnorm p u a b q)
            (atom.eval (I := I) P.metric hEnorm p u a b q)) <=
        B atom) ->
      forall (term : CurvJetTerm) (q : Real × Real),
        Real.sqrt
            (P.metric.inner
              (intrLaunch3 (I := I) P.metric hEnorm p u a b
                ((q.1, 0), q.2))
              (term.eval (I := I) P.metric hEnorm p u a b q)
              (term.eval (I := I) P.metric hEnorm p u a b q)) <=
          term.majorant hP.C B := by
  letI : TopologicalSpace P.M := P.topology
  letI : ChartedSpace H P.M := P.charted
  letI : IsManifold I ∞ P.M := P.smooth
  letI : SigmaCompactSpace P.M := P.sigmaCompact
  letI : T2Space P.M := P.t2
  letI : T2Space (TangentBundle I P.M) := P.t2TangentBundle
  letI : RiemannianBundle (fun x : P.M => TangentSpace I x) :=
    P.riemBundle (I := I)
  letI : (x : P.M) -> InnerProductSpace Real (TangentSpace I x) :=
    P.riemInner (I := I)
  letI : IsContinuousRiemannianBundle E
      (fun x : P.M => TangentSpace I x) :=
    P.riemBundle_cont (I := I)
  letI : EMetricSpace P.M := P.emetricSpace (I := I)
  letI : CompleteSpace P.M :=
    MetricComplete.complete (I := I) P hcomplete
  let hEnorm : forall (x : P.M) (v : TangentSpace I x),
      ‖v‖ₑ = ENNReal.ofReal
        (Real.sqrt (P.metric.inner x v v)) := by
    intro x v
    simpa using
      (Geometry.Riemannian.tensor0SBundle_enorm_eq_riemannianBundle_enorm
        (I := I) P.metric x v)
  dsimp only
  intro hatom term q
  apply CurvJetTerm.eval_le_of
    (I := I) P.metric hEnorm p u a b hP.C hP.nonneg B
  · intro k x v
    exact HasCurvDerivBound.curvOpN_le (I := I) P (hP.bound k) x v
  · exact hatom

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
private theorem IntrJetAtom.eval_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (atom : IntrJetAtom) :
    ContMDiff
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      I.tangent ∞
      (fun q : Real × Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))
          (atom.eval (I := I) g hEnorm p u a b q) :
            TangentBundle I M)) := by
  let f : Real -> Real -> M := fun r t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  let A : forall r t : Real, TangentSpace I (f r t) := fun r t =>
    varFst (I := I) f r t
  let B : forall r t : Real, TangentSpace I (f r t) := fun r t =>
    intrLaunchJ (I := I) g hEnorm p u a b (r, t)
  have hA :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (A q.1 q.2) : TangentBundle I M)) := by
    have hdir :=
      intrLaunchDir_smooth (I := I) g hEnorm p u a b
        (((1 : Real), (0 : Real)), (0 : Real))
    simpa only [f, A, intrLaunchA_eq] using hdir
  have hT :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (varSnd (I := I) f q.1 q.2) :
              TangentBundle I M)) := by
    have hdir :=
      intrLaunchDir_smooth (I := I) g hEnorm p u a b
        (((0 : Real), (0 : Real)), (1 : Real))
    simpa only [f, intrLaunchT_eq] using hdir
  have hB :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (B q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, B] using
      intrLaunchJ_smooth (I := I) g hEnorm p u a b
  cases atom with
  | pathT =>
      simpa only [IntrJetAtom.eval, f] using hT
  | pathDt =>
      have hdt :=
        cov_snd_smooth (I := I) g f
          (fun r t => varSnd (I := I) f r t) hT
      simpa only [IntrJetAtom.eval, f, covSnd] using hdt
  | aJet n =>
      have hn := covFstIter_smooth (I := I) g f A hA n
      simpa only [IntrJetAtom.eval, f, A] using hn
  | aTime n =>
      have hn := covFstIter_smooth (I := I) g f A hA n
      have hdn :=
        cov_snd_smooth (I := I) g f
          (fun r t => covFstIter (I := I) g f n A r t) hn
      simpa only [IntrJetAtom.eval, f, A, covSnd] using hdn
  | bJet n =>
      have hn := covFstIter_smooth (I := I) g f B hB n
      simpa only [IntrJetAtom.eval, f, B] using hn
  | bTime n =>
      have hn := covFstIter_smooth (I := I) g f B hB n
      have hdn :=
        cov_snd_smooth (I := I) g f
          (fun r t => covFstIter (I := I) g f n B r t) hn
      simpa only [IntrJetAtom.eval, f, B, covSnd] using hdn

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
private theorem CurvJetTerm.finSum_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) {n : Nat}
    (terms : Fin n -> CurvJetTerm) (q : Real × Real) :
    (CurvJetTerm.finSum terms).eval (I := I) g hEnorm p u a b q =
      ∑ i, (terms i).eval g hEnorm p u a b q := by
  induction n with
  | zero =>
      rw [CurvJetTerm.finSum]
      change (0 : TangentSpace I
        (intrLaunch3 (I := I) g hEnorm p u a b ((q.1, 0), q.2))) =
          ∑ i : Fin 0, (terms i).eval g hEnorm p u a b q
      simp only [Finset.univ_eq_empty, Finset.sum_empty]
  | succ n ih =>
      rw [CurvJetTerm.finSum]
      change
        (terms 0).eval g hEnorm p u a b q +
            (CurvJetTerm.finSum (fun i => terms i.succ)).eval
              g hEnorm p u a b q =
          ∑ i, (terms i).eval g hEnorm p u a b q
      rw [Fin.sum_univ_succ, ih]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
private theorem CurvJetTerm.eval_launch_smooth
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (term : CurvJetTerm) (t : Real) :
    ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun r : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t))
          (term.eval (I := I) g hEnorm p u a b (r, t)) :
            TangentBundle I M)) := by
  let gamma : Real -> M := fun r =>
    intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), t)
  have hgamma : ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
    have hincl :
        ContMDiff
          (modelWithCornersSelf Real Real)
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun r : Real => ((r, (0 : Real)), t)) :=
      (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  induction term with
  | zero =>
      let Z : ContMDiffSection I E (∞ : WithTop ℕ∞)
          (TangentSpace I : M -> Type _) := 0
      have hzero := Z.contMDiff.comp hgamma
      simpa only [CurvJetTerm.eval, gamma, Z, Function.comp_apply,
        ContMDiffSection.coe_zero, Pi.zero_apply] using hzero
  | atom atom =>
      have hincl :
          ContMDiff
            (modelWithCornersSelf Real Real)
            ((modelWithCornersSelf Real Real).prod
              (modelWithCornersSelf Real Real))
            ∞ (fun r : Real => (r, t)) :=
        contMDiff_id.prodMk contMDiff_const
      have hatom :=
        (IntrJetAtom.eval_smooth (I := I) g hEnorm p u a b atom).comp hincl
      simpa only [CurvJetTerm.eval, Function.comp_apply] using hatom
  | add x y ihx ihy =>
      let fields : Fin 2 -> forall r : Real, TangentSpace I (gamma r) :=
        Fin.cons
          (fun r => x.eval (I := I) g hEnorm p u a b (r, t))
          (fun _ r => y.eval (I := I) g hEnorm p u a b (r, t))
      have hfields : forall i, ContMDiff
          (modelWithCornersSelf Real Real) I.tangent ∞
          (fun r : Real =>
            (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
              (gamma r) (fields i r) : TangentBundle I M)) := by
        intro i
        fin_cases i
        · simpa only [fields, Fin.cons_zero, gamma] using ihx
        · simpa only [fields, Fin.cons_succ, Fin.cons_zero, gamma] using ihy
      have hsum :=
        contMDiff_sum_along (I := I)
          (Finset.univ : Finset (Fin 2)) gamma fields hgamma
          (fun i _ => hfields i)
      simpa only [CurvJetTerm.eval, fields, gamma, Fin.sum_univ_two,
        Fin.cons_zero, Fin.cons_succ] using hsum
  | scale c x ih =>
      have hc : ContMDiff (modelWithCornersSelf Real Real)
          (modelWithCornersSelf Real Real) ∞ (fun _ : Real => c) :=
        contMDiff_const
      simpa only [CurvJetTerm.eval, gamma] using
        contMDiff_smul_bundleField_perp (I := I) hgamma hc ih
  | curv k slots ih =>
      simpa only [CurvJetTerm.eval, gamma] using
        curvOpN_smoothAlong (I := I) g k gamma
          (fun i r => (slots i).eval g hEnorm p u a b (r, t))
          hgamma ih

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem IntrJetAtom.launchDeriv_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (atom : IntrJetAtom) (r t : Real) :
    covFst (I := I) g
        (fun s v : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v))
        (fun s v : Real =>
          atom.eval (I := I) g hEnorm p u a b (s, v)) r t =
      (CurvJetTerm.atom atom).launchDeriv.eval
        (I := I) g hEnorm p u a b (r, t) := by
  let f : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  let A : forall s v : Real, TangentSpace I (f s v) := fun s v =>
    varFst (I := I) f s v
  let B : forall s v : Real, TangentSpace I (f s v) := fun s v =>
    intrLaunchJ (I := I) g hEnorm p u a b (s, v)
  have hfSmooth :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hf : IsSmoothVariation (I := I) f :=
    hfSmooth.of_le ENat.LEInfty.out
  have hA :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (A q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, A, IntrJetAtom.eval, covFstIter_zero] using
      IntrJetAtom.eval_smooth (I := I) g hEnorm p u a b (.aJet 0)
  have hB :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (B q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, B, IntrJetAtom.eval, covFstIter_zero] using
      IntrJetAtom.eval_smooth (I := I) g hEnorm p u a b (.bJet 0)
  have hslots3 (x y z : CurvJetTerm) :
      (fun i =>
          (slots3 x y z i).eval (I := I) g hEnorm p u a b (r, t)) =
        DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
          (x.eval g hEnorm p u a b (r, t))
          (y.eval g hEnorm p u a b (r, t))
          (z.eval g hEnorm p u a b (r, t)) := by
    funext i
    fin_cases i <;> rfl
  cases atom with
  | pathT =>
      have hcomm :=
        commute_ds_dt_intrinsic_shifted (I := I) g f hf t
      simpa only [CurvJetTerm.launchDeriv, CurvJetTerm.eval,
        IntrJetAtom.eval, covFstIter_zero, f, A, covFst, covSnd,
        varFst, varSnd] using congrFun hcomm r
  | pathDt =>
      have hzero :
          (fun s : Real =>
            IntrJetAtom.pathDt.eval (I := I) g hEnorm p u a b (s, t)) =
            fun s : Real => (0 : TangentSpace I (f s t)) := by
        funext s
        let gamma : Real -> M := fun v => f s v
        have hgamma :
            ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
          have hincl :
              ContMDiff
                (modelWithCornersSelf Real Real)
                ((modelWithCornersSelf Real Real).prod
                  (modelWithCornersSelf Real Real))
                ∞ (fun v : Real => (s, v)) :=
            contMDiff_const.prodMk contMDiff_id
          exact hfSmooth.comp hincl
        have hgeo :
            DifferentialGeometry.Geometry.Riemannian.Geodesic.IsGeodesic
              (I := I) g gamma := by
          simpa only [gamma, f, intrLaunch3, zero_smul, add_zero] using
            intrinsicGeodesic_isGeodesic (I := I) g hEnorm p
              (show TangentSpace I p from u + s • a)
        have hz :=
          (covDerivAlong_velocity_eq_zero_iff_hasGeodesicEquationAt
            (I := I) g gamma t hgamma).2
            (hgeo.hasGeodesicEquationAt t)
        simpa only [IntrJetAtom.eval, f, gamma, covSnd, varSnd] using hz
      change
        covDerivAlong (I := I) g (fun s : Real => f s t)
            (fun s : Real =>
              IntrJetAtom.pathDt.eval (I := I) g hEnorm p u a b (s, t)) r =
          0
      rw [hzero]
      exact covDerivAlong_zero (I := I) g (fun s : Real => f s t) r
  | aJet n =>
      rfl
  | aTime n =>
      have hn := covFstIter_smooth (I := I) g f A hA n
      have hcomm :=
        cov_commute_at (I := I) g f hf
          (fun s v => covFstIter (I := I) g f n A s v) hn r t
      have hsum :
          covFst (I := I) g f
                (fun s v =>
                  covSnd (I := I) g f
                    (fun x y => covFstIter (I := I) g f n A x y) s v) r t =
            covSnd (I := I) g f
                (fun s v =>
                  covFst (I := I) g f
                    (fun x y => covFstIter (I := I) g f n A x y) s v) r t +
              varCurv (I := I) g f
                (fun s v => covFstIter (I := I) g f n A s v) r t := by
        calc
          _ = (covFst (I := I) g f
                  (fun s v =>
                    covSnd (I := I) g f
                      (fun x y => covFstIter (I := I) g f n A x y) s v) r t -
                covSnd (I := I) g f
                  (fun s v =>
                    covFst (I := I) g f
                      (fun x y => covFstIter (I := I) g f n A x y) s v) r t) +
              covSnd (I := I) g f
                (fun s v =>
                  covFst (I := I) g f
                    (fun x y => covFstIter (I := I) g f n A x y) s v) r t := by
                abel
          _ = _ := by
            rw [hcomm]
            abel
      simpa only [CurvJetTerm.launchDeriv, CurvJetTerm.eval,
        IntrJetAtom.eval, f, A, covFstIter_succ, varCurv,
        curvAlong_eq_op0, hslots3] using hsum
  | bJet n =>
      rfl
  | bTime n =>
      have hn := covFstIter_smooth (I := I) g f B hB n
      have hcomm :=
        cov_commute_at (I := I) g f hf
          (fun s v => covFstIter (I := I) g f n B s v) hn r t
      have hsum :
          covFst (I := I) g f
                (fun s v =>
                  covSnd (I := I) g f
                    (fun x y => covFstIter (I := I) g f n B x y) s v) r t =
            covSnd (I := I) g f
                (fun s v =>
                  covFst (I := I) g f
                    (fun x y => covFstIter (I := I) g f n B x y) s v) r t +
              varCurv (I := I) g f
                (fun s v => covFstIter (I := I) g f n B s v) r t := by
        calc
          _ = (covFst (I := I) g f
                  (fun s v =>
                    covSnd (I := I) g f
                      (fun x y => covFstIter (I := I) g f n B x y) s v) r t -
                covSnd (I := I) g f
                  (fun s v =>
                    covFst (I := I) g f
                      (fun x y => covFstIter (I := I) g f n B x y) s v) r t) +
              covSnd (I := I) g f
                (fun s v =>
                  covFst (I := I) g f
                    (fun x y => covFstIter (I := I) g f n B x y) s v) r t := by
                abel
          _ = _ := by
            rw [hcomm]
            abel
      simpa only [CurvJetTerm.launchDeriv, CurvJetTerm.eval,
        IntrJetAtom.eval, f, B, covFstIter_succ, varCurv,
        curvAlong_eq_op0, hslots3] using hsum

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
private theorem IntrJetAtom.covFst_time0_of_const
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b c : E) (atom : IntrJetAtom)
    (hconst : forall s,
      atom.eval (I := I) g hEnorm p u a b (s, 0) = c)
    (r : Real) :
    covFst (I := I) g
        (fun s t : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t))
        (fun s t : Real => atom.eval (I := I) g hEnorm p u a b (s, t))
        r 0 = 0 := by
  let f : Real -> Real -> M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
  let V : forall s t : Real, TangentSpace I (f s t) := fun s t =>
    atom.eval (I := I) g hEnorm p u a b (s, t)
  have hcurve : (fun s : Real => f s 0) =ᶠ[𝓝 r] fun _ : Real => p := by
    filter_upwards with s
    exact intrinsicGeodesic_zero (I := I) g hEnorm p _
  have hfield : ∀ᶠ s in 𝓝 r, (V s 0 : E) = c := by
    filter_upwards with s
    exact congrArg (fun z => (z : E)) (hconst s)
  have hcongr :=
    covDerivAlong_congr_curve (I := I) g
      (fun s : Real => V s 0)
      (fun _ : Real => (show TangentSpace I p from c))
      hcurve hfield
  have hflat :=
    covDerivAlong_const (I := I) g p
      (fun _ : Real => (show TangentSpace I p from c)) r (by fun_prop)
  change (covDerivAlong (I := I) g (fun s : Real => f s 0)
    (fun s : Real => V s 0) r : E) = 0
  calc
    _ = (covDerivAlong (I := I) g (fun _ : Real => p)
          (fun _ : Real => (show TangentSpace I p from c)) r : E) := hcongr
    _ = deriv (fun _ : Real => (c : E)) r := hflat
    _ = 0 := deriv_const _ _

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.aTime_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r : Real) :
    (IntrJetAtom.aTime 0).eval (I := I) g hEnorm p u a b (r, 0) = a := by
  let f : Real -> Real -> M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), t)
  let fA : Real -> Real -> M := fun s t =>
    intrLaunch3 (I := I) g hEnorm p u a a ((s, 0), t)
  let A : forall s t : Real, TangentSpace I (f s t) := fun s t =>
    varFst (I := I) f s t
  let B : forall s t : Real, TangentSpace I (f s t) := fun s t =>
    intrLaunchJ (I := I) g hEnorm p u a a (s, t)
  have hf : f = fA := by
    funext s t
    simp only [f, fA, intrLaunch3, zero_smul, add_zero]
  change covSnd (I := I) g f A r 0 = a
  have hAB : A = B := by
    funext s t
    change varFst (I := I) f s t =
      intrLaunchJ (I := I) g hEnorm p u a a (s, t)
    rw [hf]
    exact intrLaunchA_self (I := I) g hEnorm p u a s t
  rw [hAB]
  rw [hf]
  exact intrLaunchDJ_time0 (I := I) g hEnorm p u a a r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
theorem IntrJetAtom.bTime_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (r : Real) :
    (IntrJetAtom.bTime 0).eval (I := I) g hEnorm p u a b (r, 0) = b := by
  simpa only [IntrJetAtom.eval, covFstIter_zero] using
    intrLaunchDJ_time0 (I := I) g hEnorm p u a b r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
omit [CompleteSpace E] in
private theorem IntrJetAtom.timeCurv_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (jet : IntrJetAtom) (r : Real) :
    (CurvJetTerm.curv 0
        (slots3 (CurvJetTerm.atom (.aJet 0))
          (CurvJetTerm.atom .pathT) (CurvJetTerm.atom jet))).eval
        (I := I) g hEnorm p u a b (r, 0) = 0 := by
  change curvOpN (I := I) g 0
      (intrLaunch3 (I := I) g hEnorm p u a b ((r, 0), 0))
      (fun i =>
        (slots3 (CurvJetTerm.atom (.aJet 0))
          (CurvJetTerm.atom .pathT) (CurvJetTerm.atom jet) i).eval
            (I := I) g hEnorm p u a b (r, 0)) = 0
  apply curvOpN_zero_at (I := I) g 0 _ _ (0 : Fin 3)
  change (IntrJetAtom.aJet 0).eval
    (I := I) g hEnorm p u a b (r, 0) = 0
  exact IntrJetAtom.aJet_time0 (I := I) g hEnorm p u a b 0 r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
private theorem IntrJetAtom.time_succ_zero
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b c : E) (time jet next : IntrJetAtom)
    (hlaunch :
      (CurvJetTerm.atom time).launchDeriv =
        CurvJetTerm.atom next +
          CurvJetTerm.curv 0
            (slots3 (CurvJetTerm.atom (.aJet 0))
              (CurvJetTerm.atom .pathT) (CurvJetTerm.atom jet)))
    (hconst : forall s,
      time.eval (I := I) g hEnorm p u a b (s, 0) = c)
    (r : Real) :
    next.eval (I := I) g hEnorm p u a b (r, 0) = 0 := by
  have hstep :=
    IntrJetAtom.launchDeriv_eval
      (I := I) g hEnorm p u a b time r 0
  have hleft :=
    IntrJetAtom.covFst_time0_of_const
      (I := I) g hEnorm p u a b c time hconst r
  rw [hleft, hlaunch] at hstep
  simp only [CurvJetTerm.eval] at hstep
  have hcurv :=
    IntrJetAtom.timeCurv_time0
      (I := I) g hEnorm p u a b jet r
  simp only [CurvJetTerm.eval] at hcurv
  rw [hcurv, add_zero] at hstep
  exact hstep.symm

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem IntrJetAtom.aTime_succ_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    forall n r,
      (IntrJetAtom.aTime (n + 1)).eval
        (I := I) g hEnorm p u a b (r, 0) = 0 := by
  intro n
  induction n with
  | zero =>
      intro r
      exact IntrJetAtom.time_succ_zero
        (I := I) g hEnorm p u a b a
        (.aTime 0) (.aJet 0) (.aTime 1) rfl
        (IntrJetAtom.aTime_zero (I := I) g hEnorm p u a b) r
  | succ n ih =>
      intro r
      exact IntrJetAtom.time_succ_zero
        (I := I) g hEnorm p u a b 0
        (.aTime (n + 1)) (.aJet (n + 1)) (.aTime (n + 1 + 1)) rfl ih r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem IntrJetAtom.bTime_succ_time0
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) :
    forall n r,
      (IntrJetAtom.bTime (n + 1)).eval
        (I := I) g hEnorm p u a b (r, 0) = 0 := by
  intro n
  induction n with
  | zero =>
      intro r
      exact IntrJetAtom.time_succ_zero
        (I := I) g hEnorm p u a b b
        (.bTime 0) (.bJet 0) (.bTime 1) rfl
        (IntrJetAtom.bTime_zero (I := I) g hEnorm p u a b) r
  | succ n ih =>
      intro r
      exact IntrJetAtom.time_succ_zero
        (I := I) g hEnorm p u a b 0
        (.bTime (n + 1)) (.bJet (n + 1)) (.bTime (n + 1 + 1)) rfl ih r

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem CurvJetTerm.launchDeriv_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (term : CurvJetTerm) (r t : Real) :
    covFst (I := I) g
        (fun s v : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v))
        (fun s v : Real =>
          term.eval (I := I) g hEnorm p u a b (s, v)) r t =
      term.launchDeriv.eval (I := I) g hEnorm p u a b (r, t) := by
  classical
  let f : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  induction term with
  | zero =>
      change
        covDerivAlong (I := I) g (fun s : Real => f s t)
            (fun s : Real => (0 : TangentSpace I (f s t))) r = 0
      exact covDerivAlong_zero (I := I) g (fun s : Real => f s t) r
  | atom atom =>
      exact IntrJetAtom.launchDeriv_eval
        (I := I) g hEnorm p u a b atom r t
  | add x y ihx ihy =>
      let gamma : Real -> M := fun s => f s t
      let X : forall s : Real, TangentSpace I (gamma s) := fun s =>
        x.eval (I := I) g hEnorm p u a b (s, t)
      let Y : forall s : Real, TangentSpace I (gamma s) := fun s =>
        y.eval (I := I) g hEnorm p u a b (s, t)
      have hX := CurvJetTerm.eval_launch_smooth
        (I := I) g hEnorm p u a b x t
      have hY := CurvJetTerm.eval_launch_smooth
        (I := I) g hEnorm p u a b y t
      have hadd :=
        covDerivAlong_add (I := I) g gamma X Y r
          (chartRep_diff (I := I) gamma X hX r)
          (chartRep_diff (I := I) gamma Y hY r)
      calc
        covFst (I := I) g f
            (fun s v =>
              (x + y).eval (I := I) g hEnorm p u a b (s, v)) r t =
            covFst (I := I) g f
                (fun s v => x.eval (I := I) g hEnorm p u a b (s, v)) r t +
              covFst (I := I) g f
                (fun s v => y.eval (I := I) g hEnorm p u a b (s, v)) r t := by
          simpa only [CurvJetTerm.eval, covFst, f, gamma, X, Y] using hadd
        _ = (x.launchDeriv + y.launchDeriv).eval
              (I := I) g hEnorm p u a b (r, t) := by
          rw [ihx, ihy]
          rfl
  | scale c x ih =>
      have hsmul :=
        covDerivAlong_smul (I := I) g (fun s : Real => f s t) c
          (fun s : Real => x.eval (I := I) g hEnorm p u a b (s, t)) r
      calc
        covFst (I := I) g f
            (fun s v =>
              (c • x).eval (I := I) g hEnorm p u a b (s, v)) r t =
            c • covFst (I := I) g f
              (fun s v => x.eval (I := I) g hEnorm p u a b (s, v)) r t := by
          simpa only [CurvJetTerm.eval, covFst, f] using hsmul
        _ = (c • x.launchDeriv).eval
              (I := I) g hEnorm p u a b (r, t) := by
          rw [ih]
          rfl
  | curv k slots ih =>
      let gamma : Real -> M := fun s => f s t
      let Y : Fin (k + 3) -> forall s : Real, TangentSpace I (gamma s) :=
        fun i s => (slots i).eval (I := I) g hEnorm p u a b (s, t)
      have hgamma :
          ContMDiff (modelWithCornersSelf Real Real) I ∞ gamma := by
        have hincl :
            ContMDiff
              (modelWithCornersSelf Real Real)
              (((modelWithCornersSelf Real Real).prod
                (modelWithCornersSelf Real Real)).prod
                  (modelWithCornersSelf Real Real))
              ∞ (fun s : Real => ((s, (0 : Real)), t)) :=
          (contMDiff_id.prodMk contMDiff_const).prodMk contMDiff_const
        exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
      have hY : forall i, ContMDiff
          (modelWithCornersSelf Real Real) I.tangent ∞
          (fun s : Real =>
            (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
              (gamma s) (Y i s) : TangentBundle I M)) := by
        intro i
        simpa only [gamma, Y, f] using
          CurvJetTerm.eval_launch_smooth
            (I := I) g hEnorm p u a b (slots i) t
      have hcurv :=
        curvOpN_covAlong (I := I) g k gamma Y r hgamma hY
      have hvel :
          ((mfderiv (modelWithCornersSelf Real Real) I gamma r :
              Real →L[Real] TangentSpace I (gamma r)) (1 : Real)) =
            (CurvJetTerm.atom (.aJet 0)).eval
              (I := I) g hEnorm p u a b (r, t) := by
        rfl
      have hslot (i : Fin (k + 3)) :
          covDerivAlong (I := I) g gamma (Y i) r =
            (slots i).launchDeriv.eval
              (I := I) g hEnorm p u a b (r, t) := by
        simpa only [covFst, gamma, Y, f] using ih i
      have hlead :
          covDerivAlong (I := I) g gamma
              (fun s : Real =>
                curvOpN (I := I) g k (gamma s) (fun i => Y i s)) r =
            curvOpN (I := I) g (k + 1) (gamma r)
                (Fin.cons
                  ((mfderiv (modelWithCornersSelf Real Real) I gamma r :
                    Real →L[Real] TangentSpace I (gamma r)) (1 : Real))
                  (fun i => Y i r)) +
              ∑ i : Fin (k + 3),
                curvOpN (I := I) g k (gamma r)
                  (Function.update (fun j => Y j r) i
                    (covDerivAlong (I := I) g gamma (Y i) r)) := by
        calc
          _ = (covDerivAlong (I := I) g gamma
                  (fun s : Real =>
                    curvOpN (I := I) g k (gamma s) (fun i => Y i s)) r -
                ∑ i : Fin (k + 3),
                  curvOpN (I := I) g k (gamma r)
                    (Function.update (fun j => Y j r) i
                      (covDerivAlong (I := I) g gamma (Y i) r))) +
              ∑ i : Fin (k + 3),
                curvOpN (I := I) g k (gamma r)
                  (Function.update (fun j => Y j r) i
                    (covDerivAlong (I := I) g gamma (Y i) r)) := by
              abel
          _ = _ := by
            rw [show
              covDerivAlong (I := I) g gamma
                    (fun s : Real =>
                      curvOpN (I := I) g k (gamma s) (fun i => Y i s)) r -
                  ∑ i : Fin (k + 3),
                    curvOpN (I := I) g k (gamma r)
                      (Function.update (fun j => Y j r) i
                        (covDerivAlong (I := I) g gamma (Y i) r)) =
                curvOpN (I := I) g (k + 1) (gamma r)
                  (Fin.cons
                    ((mfderiv (modelWithCornersSelf Real Real) I gamma r :
                      Real →L[Real] TangentSpace I (gamma r)) (1 : Real))
                    (fun i => Y i r)) by
              simpa only [curvOpNDerivAlong] using hcurv]
      have hnext :
          curvOpN (I := I) g (k + 1) (gamma r)
              (Fin.cons
                ((mfderiv (modelWithCornersSelf Real Real) I gamma r :
                  Real →L[Real] TangentSpace I (gamma r)) (1 : Real))
                (fun i => Y i r)) =
            (CurvJetTerm.curv (k + 1)
              (Fin.cons (CurvJetTerm.atom (.aJet 0)) slots)).eval
                (I := I) g hEnorm p u a b (r, t) := by
        change curvOpN (I := I) g (k + 1) (gamma r) _ =
          curvOpN (I := I) g (k + 1) (gamma r) _
        congr 1
        funext j
        refine Fin.cases ?_ (fun i => ?_) j
        · exact hvel
        · rfl
      have hupdate (i : Fin (k + 3)) :
          curvOpN (I := I) g k (gamma r)
              (Function.update (fun j => Y j r) i
                (covDerivAlong (I := I) g gamma (Y i) r)) =
            (CurvJetTerm.curv k
              (Function.update slots i (slots i).launchDeriv)).eval
                (I := I) g hEnorm p u a b (r, t) := by
        change curvOpN (I := I) g k (gamma r) _ =
          curvOpN (I := I) g k (gamma r) _
        congr 1
        funext j
        by_cases hji : j = i
        · subst j
          rw [Function.update_self, Function.update_self, hslot]
        · rw [Function.update_of_ne hji, Function.update_of_ne hji]
      have hsum :
          (∑ i : Fin (k + 3),
              curvOpN (I := I) g k (gamma r)
                (Function.update (fun j => Y j r) i
                  (covDerivAlong (I := I) g gamma (Y i) r))) =
            (CurvJetTerm.finSum (fun i =>
              CurvJetTerm.curv k
                (Function.update slots i (slots i).launchDeriv))).eval
                  (I := I) g hEnorm p u a b (r, t) := by
        rw [CurvJetTerm.finSum_eval]
        apply Finset.sum_congr rfl
        intro i hi
        exact hupdate i
      change
        covDerivAlong (I := I) g gamma
            (fun s : Real =>
              curvOpN (I := I) g k (gamma s) (fun i => Y i s)) r =
          (CurvJetTerm.curv (k + 1)
                (Fin.cons (CurvJetTerm.atom (.aJet 0)) slots)).eval
              (I := I) g hEnorm p u a b (r, t) +
            (CurvJetTerm.finSum (fun i =>
              CurvJetTerm.curv k
                (Function.update slots i (slots i).launchDeriv))).eval
                  (I := I) g hEnorm p u a b (r, t)
      rw [hlead, hnext, hsum]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem CurvJetTerm.launchIter_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (m : Nat) (term : CurvJetTerm) :
    covFstIter (I := I) g
        (fun s v : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v))
        m (fun s v : Real =>
          term.eval (I := I) g hEnorm p u a b (s, v)) =
      fun s v : Real =>
        (term.launchIter m).eval (I := I) g hEnorm p u a b (s, v) := by
  induction m with
  | zero =>
      rfl
  | succ m ih =>
      funext r t
      rw [covFstIter_succ, ih]
      exact CurvJetTerm.launchDeriv_eval
        (I := I) g hEnorm p u a b (term.launchIter m) r t

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrCorrTerm_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) (r t : Real) :
    intrJetCorr (I := I) g hEnorm p u a b n (r, t) =
      (intrCorrTerm n).eval (I := I) g hEnorm p u a b (r, t) := by
  let f : Real -> Real -> M := fun s v =>
    intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v)
  let A : forall s v : Real, TangentSpace I (f s v) := fun s v =>
    varFst (I := I) f s v
  let B : forall s v : Real, TangentSpace I (f s v) := fun s v =>
    intrLaunchJ (I := I) g hEnorm p u a b (s, v)
  let W : forall s v : Real, TangentSpace I (f s v) := fun s v =>
    covFstIter (I := I) g f n B s v
  have hf :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I ∞ (fun q : Real × Real => f q.1 q.2) := by
    have hincl :
        ContMDiff
          ((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real))
          (((modelWithCornersSelf Real Real).prod
            (modelWithCornersSelf Real Real)).prod
              (modelWithCornersSelf Real Real))
          ∞ (fun q : Real × Real => ((q.1, (0 : Real)), q.2)) :=
      (contMDiff_fst.prodMk contMDiff_const).prodMk contMDiff_snd
    exact (intrLaunch3_smooth (I := I) g hEnorm p u a b).comp hincl
  have hA :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (A q.1 q.2) : TangentBundle I M)) := by
    have hdir :=
      intrLaunchDir_smooth (I := I) g hEnorm p u a b
        (((1 : Real), (0 : Real)), (0 : Real))
    simpa only [f, A, intrLaunchA_eq] using hdir
  have hT :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (varSnd (I := I) f q.1 q.2) :
              TangentBundle I M)) := by
    have hdir :=
      intrLaunchDir_smooth (I := I) g hEnorm p u a b
        (((0 : Real), (0 : Real)), (1 : Real))
    simpa only [f, intrLaunchT_eq] using hdir
  have hW :
      ContMDiff
        ((modelWithCornersSelf Real Real).prod
          (modelWithCornersSelf Real Real))
        I.tangent ∞
        (fun q : Real × Real =>
          (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
            (f q.1 q.2) (W q.1 q.2) : TangentBundle I M)) := by
    simpa only [f, B, W, intrLaunchJet] using
      intrLaunchJet_smooth (I := I) g hEnorm p u a b n
  have htime : ContMDiff
      (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ∞ (fun v : Real => (r, v)) :=
    contMDiff_const.prodMk contMDiff_id
  have hlaunch : ContMDiff
      (modelWithCornersSelf Real Real)
      ((modelWithCornersSelf Real Real).prod
        (modelWithCornersSelf Real Real))
      ∞ (fun s : Real => (s, t)) :=
    contMDiff_id.prodMk contMDiff_const
  have hgammaT : ContMDiff (modelWithCornersSelf Real Real) I ∞
      (fun v : Real => f r v) := by
    simpa only [Function.comp_apply] using hf.comp htime
  have hgammaA : ContMDiff (modelWithCornersSelf Real Real) I ∞
      (fun s : Real => f s t) := by
    simpa only [Function.comp_apply] using hf.comp hlaunch
  have hAT : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun v : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f r v) (A r v) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using hA.comp htime
  have hAA : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f s t) (A s t) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using hA.comp hlaunch
  have hTT : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun v : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f r v) (varSnd (I := I) f r v) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using hT.comp htime
  have hTA : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f s t) (varSnd (I := I) f s t) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using hT.comp hlaunch
  have hWT : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun v : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f r v) (W r v) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using hW.comp htime
  have hWA : ContMDiff (modelWithCornersSelf Real Real) I.tangent ∞
      (fun s : Real =>
        (TotalSpace.mk' E (E := (TangentSpace I : M -> Type _))
          (f s t) (W s t) : TangentBundle I M)) := by
    simpa only [Function.comp_apply] using hW.comp hlaunch
  have hderivT :
      curvDerivAlong (I := I) g (fun v : Real => f r v)
          (fun v => A r v)
          (fun v => varSnd (I := I) f r v)
          (fun v => W r v) t =
        curvOpN (I := I) g 1 (f r t)
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (varSnd (I := I) f r t) (A r t)
            (varSnd (I := I) f r t) (W r t)) := by
    simpa only [varSnd] using
      curvDeriv_eq_op1 (I := I) g (fun v : Real => f r v)
        (fun v => A r v) (fun v => varSnd (I := I) f r v)
        (fun v => W r v) t hgammaT hAT hTT hWT
  have hderivA :
      curvDerivAlong (I := I) g (fun s : Real => f s t)
          (fun s => W s t)
          (fun s => varSnd (I := I) f s t)
          (fun s => varSnd (I := I) f s t) r =
        curvOpN (I := I) g 1 (f r t)
          (DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
            (A r t) (W r t)
            (varSnd (I := I) f r t)
            (varSnd (I := I) f r t)) := by
    simpa only [A, varFst] using
      curvDeriv_eq_op1 (I := I) g (fun s : Real => f s t)
        (fun s => W s t) (fun s => varSnd (I := I) f s t)
        (fun s => varSnd (I := I) f s t) r hgammaA hWA hTA hTA
  have hslots3 (x y z : CurvJetTerm) :
      (fun i =>
          (slots3 x y z i).eval (I := I) g hEnorm p u a b (r, t)) =
        DifferentialGeometry.Geometry.Curvature.vec3 (I := I)
          (x.eval g hEnorm p u a b (r, t))
          (y.eval g hEnorm p u a b (r, t))
          (z.eval g hEnorm p u a b (r, t)) := by
    funext i
    fin_cases i <;> rfl
  have hslots4 (w x y z : CurvJetTerm) :
      (fun i =>
          (slots4 w x y z i).eval (I := I) g hEnorm p u a b (r, t)) =
        DifferentialGeometry.Geometry.Curvature.vec4 (I := I)
          (w.eval g hEnorm p u a b (r, t))
          (x.eval g hEnorm p u a b (r, t))
          (y.eval g hEnorm p u a b (r, t))
          (z.eval g hEnorm p u a b (r, t)) := by
    funext i
    fin_cases i <;> rfl
  have hfvar : IsSmoothVariation (I := I) f :=
    hf.of_le ENat.LEInfty.out
  have hmix :
      covFst (I := I) g f
          (fun s v => varSnd (I := I) f s v) r t =
        covSnd (I := I) g f
          (fun s v => varFst (I := I) f s v) r t := by
    have hcomm :=
      commute_ds_dt_intrinsic_shifted (I := I) g f hfvar t
    simpa only [covFst, covSnd, varFst, varSnd] using
      congrFun hcomm r
  change jacStepCorr (I := I) g f W r t =
    (intrCorrTerm n).eval (I := I) g hEnorm p u a b (r, t)
  unfold jacStepCorr
  rw [hderivT, hderivA]
  simp only [curvAlong_eq_op0]
  rw [hmix]
  simp only [intrCorrTerm, CurvJetTerm.eval, hslots3, hslots4,
    IntrJetAtom.eval, covFstIter_zero, varCurv, curvAlong_eq_op0,
    f, A, B, W]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrResidualTerm_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (n : Nat) :
    (fun r t : Real =>
      intrJetResidual (I := I) g hEnorm p u a b n (r, t)) =
        fun r t : Real =>
          (intrResidualTerm n).eval
            (I := I) g hEnorm p u a b (r, t) := by
  induction n with
  | zero =>
      funext r t
      rw [intrJetResidual_zero]
      rfl
  | succ n ih =>
      funext r t
      rw [intrJetResidual_succ]
      rw [ih]
      rw [CurvJetTerm.launchDeriv_eval
        (I := I) g hEnorm p u a b (intrResidualTerm n) r t]
      rw [intrCorrTerm_eval (I := I) g hEnorm p u a b n r t]
      simp only [intrResidualTerm, CurvJetTerm.eval, sub_eq_add_neg,
        neg_one_smul]

attribute [-instance] Tensor0SBundle.tangentSpace_normedAddCommGroup
  Tensor0SBundle.tangentSpace_normedSpace in
theorem intrCorrIter_eval
    [PseudoEMetricSpace M]
    [IsRiemannianManifold I M] [CompleteSpace M]
    [IsContinuousRiemannianBundle E (fun x : M => TangentSpace I x)]
    (g : SmoothRiemannianMetric I M)
    (hEnorm : forall x : M, forall v : TangentSpace I x,
      ‖v‖ₑ = ENNReal.ofReal (Real.sqrt (g.inner x v v)))
    (p : M) (u a b : E) (m n : Nat) :
    covFstIter (I := I) g
        (fun s v : Real =>
          intrLaunch3 (I := I) g hEnorm p u a b ((s, 0), v))
        m (fun s v : Real =>
          intrJetCorr (I := I) g hEnorm p u a b n (s, v)) =
      fun s v : Real =>
        ((intrCorrTerm n).launchIter m).eval
          (I := I) g hEnorm p u a b (s, v) := by
  have hcorr :
      (fun s v : Real =>
        intrJetCorr (I := I) g hEnorm p u a b n (s, v)) =
        fun s v : Real =>
          (intrCorrTerm n).eval (I := I) g hEnorm p u a b (s, v) := by
    funext s v
    exact intrCorrTerm_eval (I := I) g hEnorm p u a b n s v
  rw [hcorr]
  exact CurvJetTerm.launchIter_eval
    (I := I) g hEnorm p u a b m (intrCorrTerm n)

end HCGCompactness
end DifferentialGeometry
