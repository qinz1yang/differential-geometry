import DifferentialGeometry.Bundle.Principal.Defs
import DifferentialGeometry.Bundle.TotalSpace
import DifferentialGeometry.Geometry.LieGroup.Representation
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section

open Set Bundle
open scoped Manifold ContDiff Bundle

structure PrincipalConnectionForm
    {k : Type*} [NontriviallyNormedField k]
    {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
    {H : Type*} [TopologicalSpace H] (I : ModelWithCorners k E H)
    (G : Type*) [Group G] [TopologicalSpace G] [ChartedSpace H G]
    {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
    {HP : Type*} [TopologicalSpace HP] (IP : ModelWithCorners k EP HP)
    {B : Type*} [TopologicalSpace B] (P : B → Type*) [∀ x, Torsor G (P x)]
    [∀ x, TopologicalSpace (P x)] [TopologicalSpace (TotalSpace G P)]
    [FiberBundle G P] [IsPrincipalBundle P]
    [ChartedSpace HP (TotalSpace G P)] [IsManifold IP 1 (TotalSpace G P)] (n : ℕ∞ω) where
  toFun : ∀ p : TotalSpace G P, TangentSpace IP p →L[k] GroupLieAlgebra I G
  contMDiff : ContMDiff (M' := E) IP.tangent 𝓘(k, E) n
    (fun z : TangentBundle IP (TotalSpace G P) => (toFun z.proj z.snd : E))
  apply_fundamental (p : TotalSpace G P) (U : GroupLieAlgebra I G) :
    toFun p (mfderiv I IP (fun g : G => g • p) 1 U) = U
  apply_smul (g : G) (p : TotalSpace G P) (X : TangentSpace IP p) :
    toFun (g • p) (mfderiv IP IP (fun q => g • q) p X) =
      mfderiv I I (fun h => g * h * g⁻¹) 1 (toFun p X)

namespace ContRepresentation

variable {k : Type*} [NontriviallyNormedField k]
  {E : Type*} [NormedAddCommGroup E] [NormedSpace k E]
  {H : Type*} [TopologicalSpace H] {I : ModelWithCorners k E H}
  {G : Type*} [Group G] [TopologicalSpace G] [ChartedSpace H G]
  {W : Type*} [NormedAddCommGroup W] [NormedSpace k W]
  {EP : Type*} [NormedAddCommGroup EP] [NormedSpace k EP]
  {HP : Type*} [TopologicalSpace HP] {IP : ModelWithCorners k EP HP}
  {P : Type*} [TopologicalSpace P] [ChartedSpace HP P]

def covariantDifferential (ρ : ContRepresentation k G W)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G) (f : P → W) (p : P) :
    TangentSpace IP p →L[k] W :=
  mvfderiv IP f p - ((ContinuousLinearMap.apply k W (f p)).comp
    (mvfderiv I (fun g => ρ g) 1)).comp (form p)

theorem covariantDifferential_apply (ρ : ContRepresentation k G W)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G) (f : P → W)
    (p : P) (X : TangentSpace IP p) :
    ρ.covariantDifferential form f p X =
      mvfderiv IP f p X - mvfderiv I (fun g => ρ g) 1 (form p X) (f p) := rfl

theorem covariantDifferential_eq_mvfderiv_of_horizontal
    (ρ : ContRepresentation k G W)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G) (f : P → W)
    {p : P} {X : TangentSpace IP p} (hX : form p X = 0) :
    ρ.covariantDifferential form f p X = mvfderiv IP f p X := by
  rw [ρ.covariantDifferential_apply, hX, map_zero, zero_apply, sub_zero]

theorem covariantDifferential_add (ρ : ContRepresentation k G W)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    {f g : P → W} {p : P} (hf : MDifferentiableAt IP 𝓘(k, W) f p)
    (hg : MDifferentiableAt IP 𝓘(k, W) g p) :
    ρ.covariantDifferential form (f + g) p =
      ρ.covariantDifferential form f p + ρ.covariantDifferential form g p := by
  ext X
  simp only [ρ.covariantDifferential_apply, mvfderiv_add hf hg, add_apply, Pi.add_apply, map_add]
  abel

theorem covariantDifferential_smul_function (ρ : ContRepresentation k G W)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    {f : P → W} {a : P → k} {p : P} (hf : MDifferentiableAt IP 𝓘(k, W) f p)
    (ha : MDifferentiableAt IP 𝓘(k, k) a p) :
    ρ.covariantDifferential form (a • f) p =
      a p • ρ.covariantDifferential form f p + (mvfderiv IP a p).smulRight (f p) := by
  ext X
  simp only [ρ.covariantDifferential_apply, mvfderiv_smul ha hf, smul_apply, add_apply,
    ContinuousLinearMap.smulRight_apply, smul_sub]
  change a p • _ + mvfderiv IP a p X • f p -
    mvfderiv I (fun g => ρ g) 1 (form p X) (a p • f p) = _
  rw [map_smul]
  abel

theorem contMDiff_covariantDifferential [IsManifold IP 1 P]
    (ρ : ContRepresentation k G W)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    {m n : ℕ∞ω} (hmn : m + 1 ≤ n)
    (hω : ContMDiff (M' := E) IP.tangent 𝓘(k, E) m
      (fun z : TangentBundle IP P => (form z.proj z.snd : E)))
    {f : P → W} (hf : ContMDiff IP 𝓘(k, W) n f) :
    ContMDiff IP.tangent 𝓘(k, W) m
      (fun z : TangentBundle IP P => ρ.covariantDifferential form f z.proj z.snd) := by
  have hd := (contMDiff_snd_tangentBundle_modelSpace W 𝓘(k, W) (n := m)).comp
    (hf.contMDiff_tangentMap hmn)
  have hdf : ContMDiff IP.tangent 𝓘(k, W) m
      (fun z : TangentBundle IP P => mvfderiv IP f z.proj z.snd) := by
    exact hd
  have hm : m ≤ n := le_self_add.trans hmn
  have hfv := (hf.of_le hm).comp (contMDiff_proj (F := EP) (TangentSpace IP))
  let L : E →L[k] W →L[k] W := mvfderiv I (fun g => ρ g) 1
  have hA := L.contMDiff.comp hω
  exact hdf.sub (hA.clm_apply hfv)


variable [MulAction G P] [ContMDiffSMul I IP 1 G P]

theorem covariantDifferential_fundamental_eq_zero (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p)) {p : P}
    (hf : MDifferentiableAt IP 𝓘(k, W) f p)
    (hω : ∀ U : GroupLieAlgebra I G, form p (mfderiv I IP (fun g : G => g • p) 1 U) = U)
    (U : GroupLieAlgebra I G) :
    ρ.covariantDifferential form f p (mfderiv I IP (fun g : G => g • p) 1 U) = 0 := by
  change mvfderiv IP f p (mfderiv I IP (fun g : G => g • p) 1 U) -
    mvfderiv I (fun g => ρ g) 1 (form p (mfderiv I IP (fun g : G => g • p) 1 U)) (f p) = 0
  have hh := ρ.mvfderiv_equivariant_fundamental hρ heq hf U
  rw [hω U]
  exact sub_eq_zero.mpr hh

include I in
private theorem mdifferentiableAt_equivariant_smul (ρ : ContRepresentation k G W)
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p)) {p : P}
    (hf : MDifferentiableAt IP 𝓘(k, W) f p) (g : G) :
    MDifferentiableAt IP 𝓘(k, W) f (g • p) := by
  have hi : MDifferentiableAt IP IP (fun q : P => g⁻¹ • q) (g • p) :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := IP) (n := 1) g⁻¹).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hf' : MDifferentiableAt IP 𝓘(k, W) f (g⁻¹ • (g • p)) := by
    simpa only [inv_smul_smul] using hf
  have h := (ρ g).mdifferentiableAt.comp (g • p) (hf'.comp (g • p) hi)
  apply h.congr_of_eventuallyEq
  apply Filter.Eventually.of_forall
  intro q
  exact (congrArg f (smul_inv_smul g q)).symm.trans (heq g (g⁻¹ • q))

include I in
private theorem mvfderiv_equivariant_smul (ρ : ContRepresentation k G W)
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p))
    (g : G) (p : P) (hf : MDifferentiableAt IP 𝓘(k, W) f p)
    (X : TangentSpace IP p) :
    mvfderiv IP f (g • p) (mfderiv IP IP (fun q => g • q) p X) =
      ρ g (mvfderiv IP f p X) := by
  have hg : MDifferentiableAt IP IP (fun q : P => g • q) p :=
    ((ContMDiffSMul.contMDiff_const_smul (I := I) (I' := IP) (n := 1) g).contMDiffAt :
      ContMDiffAt IP IP 1 (fun q : P => g • q) p).mdifferentiableAt (by simp)
  have h := MDifferentiableAt.mvfderiv_comp_apply
    (f := fun q : P => g • q) (g := f) (x := p) (ρ.mdifferentiableAt_equivariant_smul (I := I) heq hf g) hg X
  have hc := congrArg (fun L => L X)
    ((mdifferentiableAt_const (c := ρ g)).mvfderiv_clm_apply hf)
  simp only [mvfderiv_const, ContinuousLinearMap.comp_zero, add_zero,
    ContinuousLinearMap.comp_apply] at hc
  have he : (f ∘ fun q : P => g • q) = fun q => ρ g (f q) := by
    funext q
    exact heq g q
  rw [he] at h
  exact h.symm.trans hc

theorem covariantDifferential_smul [ContMDiffMul I 1 G]
    (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    (hω : ∀ (g : G) (p : P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv I I (fun h => g * h * g⁻¹) 1 (form p X))
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p))
    (g : G) (p : P) (hf : MDifferentiableAt IP 𝓘(k, W) f p)
    (X : TangentSpace IP p) :
    ρ.covariantDifferential form f (g • p) (mfderiv IP IP (fun q => g • q) p X) =
      ρ g (ρ.covariantDifferential form f p X) := by
  rw [ρ.covariantDifferential_apply, ρ.covariantDifferential_apply,
    ρ.mvfderiv_equivariant_smul (I := I) heq g p hf, map_sub, heq, hω]
  have h := ρ.mvfderiv_conj_one_apply hρ g (form p X) (ρ g (f p))
  have hi : ρ g⁻¹ (ρ g (f p)) = f p := by
    rw [← mul_apply_eq_comp, ← map_mul, inv_mul_cancel, map_one]
    rfl
  rw [hi] at h
  rw [h]

theorem covariantDifferential_eq_of_sub_eq_fundamental (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p)) {p : P}
    (hf : MDifferentiableAt IP 𝓘(k, W) f p)
    (hω : ∀ U : GroupLieAlgebra I G, form p (mfderiv I IP (fun g : G => g • p) 1 U) = U)
    {X Y : TangentSpace IP p} (U : GroupLieAlgebra I G)
    (hXY : X - Y = mfderiv I IP (fun g : G => g • p) 1 U) :
    ρ.covariantDifferential form f p X = ρ.covariantDifferential form f p Y := by
  apply sub_eq_zero.mp
  rw [← map_sub, hXY]
  exact ρ.covariantDifferential_fundamental_eq_zero hρ form heq hf hω U

variable {EQ : Type*} [NormedAddCommGroup EQ] [NormedSpace k EQ]
  {HQ : Type*} [TopologicalSpace HQ] {IQ : ModelWithCorners k EQ HQ}
  {Q : Type*} [TopologicalSpace Q] [ChartedSpace HQ Q]

private theorem covariantDifferential_smul_comp_of_eq_one (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p))
    {s : Q → P} {a : Q → G} {x : Q}
    (hf : MDifferentiableAt IP 𝓘(k, W) f (s x))
    (hs : MDifferentiableAt IQ IP s x) (ha : MDifferentiableAt IQ I a x)
    (hax : a x = 1)
    (hform : ∀ U : GroupLieAlgebra I G,
      form (s x) (mfderiv I IP (fun g : G => g • s x) 1 U) = U)
    (X : TangentSpace IQ x) :
    ρ.covariantDifferential form f (a x • s x)
      (mfderiv IQ IP (fun y => a y • s y) x X) =
      ρ.covariantDifferential form f (s x) (mfderiv IQ IP s x X) := by
  have hact : MDifferentiableAt (I.prod IP) IP (fun z : G × P => z.1 • z.2) (a x, s x) :=
    (contMDiff_smul (I := I) (I' := IP) (n := 1)).contMDiffAt.mdifferentiableAt (by simp)
  have hd := congrArg (fun L => L X) (mfderiv_comp x hact (ha.prodMk hs))
  rw [mfderiv_prodMk ha hs] at hd
  change mfderiv IQ IP (fun y => a y • s y) x X =
    mfderiv (I.prod IP) IP (fun z : G × P => z.1 • z.2) (a x, s x)
      (mfderiv IQ I a x X, mfderiv IQ IP s x X) at hd
  have hsplit := mfderiv_prod_eq_add_apply (v :=
    (show TangentSpace (I.prod IP) (a x, s x) from
      (mfderiv IQ I a x X, mfderiv IQ IP s x X))) hact
  have hsplit' : mfderiv (I.prod IP) IP (fun z : G × P => z.1 • z.2) (a x, s x)
      (mfderiv IQ I a x X, mfderiv IQ IP s x X) =
      mfderiv I IP (fun g => g • s x) (a x) (mfderiv IQ I a x X) +
      mfderiv IP IP (fun q => a x • q) (s x) (mfderiv IQ IP s x X) := hsplit
  have hd' := hd.trans hsplit'
  have hone : (fun q : P => (1 : G) • q) = id := by
    funext q
    exact one_smul G q
  unfold TangentSpace at hd'
  rw [hax, hone, mfderiv_id] at hd'
  have hd'' : mfderiv IQ IP (fun y => a y • s y) x X =
      (show EP from mfderiv I IP (fun g : G => g • s x) 1 (mfderiv IQ I a x X)) +
        (show EP from mfderiv IQ IP s x X) := hd'
  have hpoint : ρ.covariantDifferential form f (a x • s x) =
      ρ.covariantDifferential form f (s x) := by
    unfold covariantDifferential TangentSpace
    rw [hax, one_smul]
  let D : EP →L[k] W := ρ.covariantDifferential form f (s x)
  have hh := congrArg (fun L => L (mfderiv IQ IP (fun y => a y • s y) x X)) hpoint
  have hsum := D.map_add
    (mfderiv I IP (fun g : G => g • s x) 1 (mfderiv IQ I a x X)) (mfderiv IQ IP s x X)
  have hzero : D (mfderiv I IP (fun g : G => g • s x) 1 (mfderiv IQ I a x X)) = 0 :=
    ρ.covariantDifferential_fundamental_eq_zero hρ form heq hf hform (mfderiv IQ I a x X)
  exact hh.trans ((congrArg D hd'').trans (hsum.trans (by rw [hzero, zero_add]; rfl)))

theorem covariantDifferential_smul_comp [ContMDiffMul I 1 G]
    (ρ : ContRepresentation k G W)
    (hρ : MDifferentiableAt I 𝓘(k, W →L[k] W) (fun g => ρ g) 1)
    (form : ∀ p : P, TangentSpace IP p →L[k] GroupLieAlgebra I G)
    (hform : ∀ (g : G) (p : P) (X : TangentSpace IP p),
      form (g • p) (mfderiv IP IP (fun q => g • q) p X) =
        mfderiv I I (fun h => g * h * g⁻¹) 1 (form p X))
    {f : P → W} (heq : ∀ g p, f (g • p) = ρ g (f p))
    {s : Q → P} {a : Q → G} {x : Q}
    (hf : MDifferentiableAt IP 𝓘(k, W) f (s x))
    (hs : MDifferentiableAt IQ IP s x) (ha : MDifferentiableAt IQ I a x)
    (hnorm : ∀ U : GroupLieAlgebra I G,
      form (s x) (mfderiv I IP (fun g : G => g • s x) 1 U) = U)
    (X : TangentSpace IQ x) :
    ρ.covariantDifferential form f (a x • s x)
      (mfderiv IQ IP (fun y => a y • s y) x X) =
      ρ (a x) (ρ.covariantDifferential form f (s x) (mfderiv IQ IP s x X)) := by
  let b : Q → G := fun y => (a x)⁻¹ * a y
  have hb : MDifferentiableAt IQ I b x := mdifferentiableAt_mul_left.comp x ha
  have hbx : b x = 1 := inv_mul_cancel (a x)
  have hbs : MDifferentiableAt IQ IP (fun y => b y • s y) x :=
    (contMDiff_smul (I := I) (I' := IP) (n := 1)).contMDiffAt.mdifferentiableAt (by simp)
      |>.comp x (hb.prodMk hs)
  have hc : MDifferentiableAt IP IP (fun p : P => a x • p) (b x • s x) :=
    (ContMDiffSMul.contMDiff_const_smul (I := I) (I' := IP) (n := 1) (a x)).contMDiffAt
      |>.mdifferentiableAt (by simp)
  have hd := congrArg (fun L => L X) (mfderiv_comp x hc hbs)
  have he : ((fun p : P => a x • p) ∘ (fun y => b y • s y)) =
      fun y => a y • s y := by
    funext y
    dsimp only [Function.comp_def, b]
    rw [← mul_smul, mul_inv_cancel_left]
  rw [he] at hd
  have hcoval := ρ.covariantDifferential_smul hρ form hform heq (a x) (b x • s x)
    (ρ.mdifferentiableAt_equivariant_smul (I := I) heq hf (b x))
    (mfderiv IQ IP (fun y => b y • s y) x X)
  have hbase : ρ.covariantDifferential form f (a x • (b x • s x)) =
      ρ.covariantDifferential form f (a x • s x) := by
    unfold covariantDifferential TangentSpace
    rw [hbx, one_smul]
  have hone := ρ.covariantDifferential_smul_comp_of_eq_one hρ form heq hf hs hb hbx hnorm X
  have hbase' := congrArg
    (fun L => L (mfderiv IP IP (fun p : P => a x • p) (b x • s x)
      (mfderiv IQ IP (fun y => b y • s y) x X))) hbase
  have hd' : mfderiv IQ IP (fun y => a y • s y) x X =
      mfderiv IP IP (fun p : P => a x • p) (b x • s x)
        (mfderiv IQ IP (fun y => b y • s y) x X) := hd
  exact (congrArg (ρ.covariantDifferential form f (a x • s x)) hd').trans
    (hbase'.symm.trans (hcoval.trans (congrArg (ρ (a x)) hone)))

end ContRepresentation
