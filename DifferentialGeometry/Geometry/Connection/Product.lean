import DifferentialGeometry.Geometry.VectorField.Product
import DifferentialGeometry.Geometry.Metric.Product
import DifferentialGeometry.Geometry.Metric.Evaluation
import DifferentialGeometry.Geometry.Connection.LeviCivita.Koszul.Formula
import DifferentialGeometry.Geometry.Connection.LeviCivita.Defs
import DifferentialGeometry.Bundle.Section
import DifferentialGeometry.Geometry.Connection.ConnectionForm
import DifferentialGeometry.Geometry.Coordinates.Frame.TangentProduct
import DifferentialGeometry.Geometry.Curvature.CurvatureOperator.Sections
import Mathlib.Geometry.Manifold.ContMDiffMFDeriv

noncomputable section
open Bundle
open scoped Manifold ContDiff
open DifferentialGeometry DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Metric DifferentialGeometry.Geometry.VectorField

namespace DifferentialGeometry.Geometry.Connection

variable {E H M F K N : Type*}
  [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
  [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]
  [NormedAddCommGroup F] [NormedSpace ℝ F] [FiniteDimensional ℝ F]
  [TopologicalSpace K] {J : ModelWithCorners ℝ F K}
  [TopologicalSpace N] [ChartedSpace K N] [IsManifold J ∞ N] [T2Space N]

omit [FiniteDimensional ℝ E] [IsManifold I ∞ M] [T2Space M]
    [FiniteDimensional ℝ F] [IsManifold J ∞ N] [T2Space N] in
private theorem mvfderiv_sum_factors {f : M → ℝ} {h : N → ℝ} (x : M × N)
    (hf : MDifferentiableAt I 𝓘(ℝ) f x.1)
    (hh : MDifferentiableAt J 𝓘(ℝ) h x.2)
    (v : TangentSpace (I.prod J) x) :
    mvfderiv (I.prod J) (fun y : M × N ↦ f y.1 + h y.2) x v =
      mvfderiv I f x.1 v.1 + mvfderiv J h x.2 v.2 := by
  have hadd := congrArg (fun L : TangentSpace (I.prod J) x →L[ℝ] ℝ ↦ L v)
    (mvfderiv_add (hf.comp x mdifferentiableAt_fst) (hh.comp x mdifferentiableAt_snd))
  have hfst := mvfderiv_comp x hf (mdifferentiableAt_fst (I := I) (I' := J))
  have hsnd := mvfderiv_comp x hh (mdifferentiableAt_snd (I := I) (I' := J))
  rw [mfderiv_fst] at hfst
  rw [mfderiv_snd] at hsnd
  exact hadd.trans (congrArg₂ (fun a b : ℝ ↦ a + b)
    (congrArg (fun L : TangentSpace (I.prod J) x →L[ℝ] ℝ ↦ L v) hfst)
    (congrArg (fun L : TangentSpace (I.prod J) x →L[ℝ] ℝ ↦ L v) hsnd))

private theorem koszulScalar_product
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y Z : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' Z' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    koszulScalar (g.prod h) (productVectorField X X')
      (productVectorField Y Y') (productVectorField Z Z') x =
        koszulScalar g X Y Z x.1 + koszulScalar h X' Y' Z' x.2 := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  have hm (A B : ContMDiffSection I E ∞ (TangentSpace I : M → Type _)) :=
    (contMDiff_metric_inner g A B).mdifferentiable (by simp) x.1
  have hn (A B : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) :=
    (contMDiff_metric_inner h A B).mdifferentiable (by simp) x.2
  simp only [koszulScalar, directionalDerivAlong]
  simp only [SmoothRiemannianMetric.prod_inner]
  simp only [mlieBracket_productVectorField, productVectorField_apply]
  linear_combination (norm := ring!)
    (mvfderiv_sum_factors x (hm Y Z) (hn Y' Z') (X x.1, X' x.2)) +
    (mvfderiv_sum_factors x (hm Z X) (hn Z' X') (Y x.1, Y' x.2)) -
    (mvfderiv_sum_factors x (hm X Y) (hn X' Y') (Z x.1, Z' x.2))

theorem leviCivita_productVectorField
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (X' Y' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _)) (x : M × N) :
    leviCivitaConnectionOfMetric (g.prod h) (productVectorField Y Y') x
        (productVectorField X X' x) =
      (leviCivitaConnectionOfMetric g Y x.1 (X x.1),
        leviCivitaConnectionOfMetric h Y' x.2 (X' x.2)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  let : CompleteSpace F := FiniteDimensional.complete ℝ F
  let m := g.prod h
  let A := leviCivitaConnectionOfMetric m (productVectorField Y Y') x
    (productVectorField X X' x)
  let B : TangentSpace (I.prod J) x :=
    (leviCivitaConnectionOfMetric g Y x.1 (X x.1),
      leviCivitaConnectionOfMetric h Y' x.2 (X' x.2))
  have htest (v : TangentSpace (I.prod J) x) : m.inner x A v = m.inner x B v := by
    obtain ⟨Z, hZ⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
      (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 v.1
    obtain ⟨Z', hZ'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
      (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 v.2
    have hv : productVectorField Z Z' x = v := Prod.ext hZ hZ'
    rw [← hv]
    change (g.prod h).inner x
        (leviCivitaConnectionOfMetric (g.prod h) (productVectorField Y Y') x
          (productVectorField X X' x)) (productVectorField Z Z' x) = _
    rw [leviCivitaConnectionOfMetric_inner_eq_koszulScalar _ _ _ _ x
      ((productVectorField X X').contMDiff.mdifferentiable (by simp) x)
      ((productVectorField Y Y').contMDiff.mdifferentiable (by simp) x)
      ((productVectorField Z Z').contMDiff.mdifferentiable (by simp) x), koszulScalar_product]
    rw [show m = g.prod h by rfl, SmoothRiemannianMetric.prod_inner]
    change (1 / 2 : ℝ) * (_ + _) =
      g.inner x.1 (leviCivitaConnectionOfMetric g Y x.1 (X x.1)) (Z x.1) +
        h.inner x.2 (leviCivitaConnectionOfMetric h Y' x.2 (X' x.2)) (Z' x.2)
    rw [leviCivitaConnectionOfMetric_inner_eq_koszulScalar _ _ _ _ x.1
      (X.contMDiff.mdifferentiable (by simp) x.1)
      (Y.contMDiff.mdifferentiable (by simp) x.1)
      (Z.contMDiff.mdifferentiable (by simp) x.1),
      leviCivitaConnectionOfMetric_inner_eq_koszulScalar _ _ _ _ x.2
      (X'.contMDiff.mdifferentiable (by simp) x.2)
      (Y'.contMDiff.mdifferentiable (by simp) x.2)
      (Z'.contMDiff.mdifferentiable (by simp) x.2)]
    ring
  exact DifferentialGeometry.Geometry.Connection.SmoothRiemannianMetric.eq_of_inner_eq m htest

theorem leviCivita_productVectorField_apply
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (Y : ContMDiffSection I E ∞ (TangentSpace I : M → Type _))
    (Y' : ContMDiffSection J F ∞ (TangentSpace J : N → Type _))
    (x : M × N) (v : TangentSpace (I.prod J) x) :
    leviCivitaConnectionOfMetric (g.prod h) (productVectorField Y Y') x v =
      (leviCivitaConnectionOfMetric g Y x.1 v.1,
        leviCivitaConnectionOfMetric h Y' x.2 v.2) := by
  obtain ⟨X, hX⟩ := ContMDiffSection.exists_eq_at (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) x.1 v.1
  obtain ⟨X', hX'⟩ := ContMDiffSection.exists_eq_at (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) x.2 v.2
  have hv : productVectorField X X' x = v := Prod.ext hX hX'
  have he := leviCivita_productVectorField g h X Y X' Y' x
  rw [hv, hX, hX'] at he
  exact he

set_option backward.isDefEq.respectTransparency false in
theorem leviCivita_prod
    (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (X Z : (x : M) → TangentSpace I x) (Y W : (x : N) → TangentSpace J x)
    (_hX : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞ (T% X))
    (hZ : ContMDiff I (I.prod (modelWithCornersSelf ℝ E)) ∞ (T% Z))
    (_hY : ContMDiff J (J.prod (modelWithCornersSelf ℝ F)) ∞ (T% Y))
    (hW : ContMDiff J (J.prod (modelWithCornersSelf ℝ F)) ∞ (T% W))
    (x : M × N) :
    (LeviCivita (I := I.prod J) (g.prod h)).toFun
        (fun p : M × N => (Z p.1, W p.2)) x (X x.1, Y x.2) =
      ((LeviCivita (I := I) g).toFun Z x.1 (X x.1),
        (LeviCivita (I := J) h).toFun W x.2 (Y x.2)) := by
  let Zs : ContMDiffSection I E ∞ (TangentSpace I : M → Type _) := ⟨Z, hZ⟩
  let Ws : ContMDiffSection J F ∞ (TangentSpace J : N → Type _) := ⟨W, hW⟩
  rw [LeviCivita_eq_leviCivitaConnectionOfMetric,
    LeviCivita_eq_leviCivitaConnectionOfMetric,
    LeviCivita_eq_leviCivitaConnectionOfMetric]
  change leviCivitaConnectionOfMetric (g.prod h) (productVectorField Zs Ws) x
      (X x.1, Y x.2) =
    (leviCivitaConnectionOfMetric g Zs x.1 (X x.1),
      leviCivitaConnectionOfMetric h Ws x.2 (Y x.2))
  exact leviCivita_productVectorField_apply g h Zs Ws x (X x.1, Y x.2)


theorem connectionForm_leviCivita_prod_of_mem (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (p : M × N) {q : M × N}
    (hq : q ∈ (trivializationAt (E × F) (TangentSpace (I.prod J)) p).baseSet)
    (v : TangentSpace (I.prod J) q) (w : E × F) :
    (LeviCivita (I := I.prod J) (g.prod h)).connectionForm
        (trivializationAt (E × F) (TangentSpace (I.prod J)) p) q v w =
      ((LeviCivita (I := I) g).connectionForm
          (trivializationAt E (TangentSpace I) p.1) q.1 v.1 w.1,
       (LeviCivita (I := J) h).connectionForm
          (trivializationAt F (TangentSpace J) p.2) q.2 v.2 w.2) := by
  have hp := hq
  have hbase : q.1 ∈ (trivializationAt E (TangentSpace I) p.1).baseSet ∧
      q.2 ∈ (trivializationAt F (TangentSpace J) p.2).baseSet := by
    simpa only [TangentBundle.trivializationAt_baseSet, prodChartedSpace_chartAt,
      OpenPartialHomeomorph.prod_source, Set.mem_prod] using hq
  have h1 := hbase.1
  have h2 := hbase.2
  obtain ⟨Y₁, hY₁⟩ := exists_contMDiffSection_eqOn_nhd (I := I) (F := E)
    (V := (TangentSpace I : M → Type _)) (n := (⊤ : ℕ∞)) (ι := Unit)
    (s := fun _ => fun y : M => (trivializationAt E (TangentSpace I) p.1).symmL ℝ y w.1)
    (u := (trivializationAt E (TangentSpace I) p.1).baseSet)
    (fun _ => Bundle.Trivialization.contMDiffOn_symmL_section (I := I)
      (trivializationAt E (TangentSpace I) p.1) w.1)
    (trivializationAt E (TangentSpace I) p.1).open_baseSet h1
  obtain ⟨Y₂, hY₂⟩ := exists_contMDiffSection_eqOn_nhd (I := J) (F := F)
    (V := (TangentSpace J : N → Type _)) (n := (⊤ : ℕ∞)) (ι := Unit)
    (s := fun _ => fun y : N => (trivializationAt F (TangentSpace J) p.2).symmL ℝ y w.2)
    (u := (trivializationAt F (TangentSpace J) p.2).baseSet)
    (fun _ => Bundle.Trivialization.contMDiffOn_symmL_section (I := J)
      (trivializationAt F (TangentSpace J) p.2) w.2)
    (trivializationAt F (TangentSpace J) p.2).open_baseSet h2
  have hY₁' : ∀ᶠ y in nhds q.1,
      (Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y
        = (trivializationAt E (TangentSpace I) p.1).symmL ℝ y w.1 :=
    hY₁.mono (fun y hy => hy ())
  have hY₂' : ∀ᶠ y in nhds q.2,
      (Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) y
        = (trivializationAt F (TangentSpace J) p.2).symmL ℝ y w.2 :=
    hY₂.mono (fun y hy => hy ())
  obtain ⟨ψ, hψdef⟩ : ∃ ψ : (y : M × N) → TangentSpace (I.prod J) y, ψ =
      fun y => (trivializationAt (E × F) (TangentSpace (I.prod J)) p).symmL ℝ y w := ⟨_, rfl⟩
  obtain ⟨φ, hφdef⟩ : ∃ φ : (y : M × N) → TangentSpace (I.prod J) y, φ =
      fun y => ((Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y.1,
        (Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) y.2) := ⟨_, rfl⟩
  rw [CovariantDerivative.connectionForm_apply _ _ hp v w,
    CovariantDerivative.connectionForm_apply _ _ h1 v.1 w.1,
    CovariantDerivative.connectionForm_apply _ _ h2 v.2 w.2]
  have hY₁p : ∀ᶠ y : M × N in nhds q,
      (Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y.1
        = (trivializationAt E (TangentSpace I) p.1).symmL ℝ y.1 w.1 :=
    ((continuous_fst : Continuous (Prod.fst : M × N → M)).continuousAt.eventually hY₁')
  have hY₂p : ∀ᶠ y : M × N in nhds q,
      (Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) y.2
        = (trivializationAt F (TangentSpace J) p.2).symmL ℝ y.2 w.2 :=
    ((continuous_snd : Continuous (Prod.snd : M × N → N)).continuousAt.eventually hY₂')
  have hsec : ψ =ᶠ[nhds q] φ := by
    rw [hψdef, hφdef]
    filter_upwards [(trivializationAt (E × F) (TangentSpace (I.prod J)) p).open_baseSet.mem_nhds hp,
      hY₁p, hY₂p] with y hy hy1 hy2
    rw [trivializationAt_symmL_prod (I := I) (J := J) p y hy, hy1, hy2]
  have hglobSmooth : ContMDiffAt (I.prod J) (I.prod J).tangent ∞ (T% φ) q := by
    rw [hφdef]
    exact (productVectorField (Y₁ ()) (Y₂ ())).contMDiff.contMDiffAt
  have hglob : MDiffAt (T% φ) q := hglobSmooth.mdifferentiableAt (by simp)
  have hsecT : (T% ψ) =ᶠ[nhds q] (T% φ) := by
    filter_upwards [hsec] with y hy
    rw [hy]
  have hloc : MDiffAt (T% ψ) q := hglob.congr_of_eventuallyEq hsecT
  have hcov2 := ((LeviCivita (I := I.prod J) (g.prod h)).isCovariantDerivativeOnUniv).congr_of_eventuallyEq
    hloc hglob Filter.univ_mem hsec
  have hcov2v : (LeviCivita (I := I.prod J) (g.prod h))
        (fun y : M × N => (trivializationAt (E × F) (TangentSpace (I.prod J)) p).symmL ℝ y w) q v =
      (LeviCivita (I := I.prod J) (g.prod h))
        (fun y : M × N => ((Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y.1,
          (Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) y.2)) q v := by
    have h := congrArg (fun L => L v) hcov2
    rwa [hψdef, hφdef] at h
  have hlev' : (LeviCivita (I := I.prod J) (g.prod h))
        (fun y : M × N => ((Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) y.1,
          (Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) y.2)) q v =
      ((LeviCivita (I := I) g) (Y₁ ()) q.1 v.1,
       (LeviCivita (I := J) h) (Y₂ ()) q.2 v.2) := by
    rw [LeviCivita_eq_leviCivitaConnectionOfMetric, LeviCivita_eq_leviCivitaConnectionOfMetric,
      LeviCivita_eq_leviCivitaConnectionOfMetric]
    exact leviCivita_productVectorField_apply g h (Y₁ ()) (Y₂ ()) q v
  rw [hcov2v, hlev']
  have hconnY₁ : (LeviCivita (I := I) g)
        (Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯) q.1 =
      (LeviCivita (I := I) g)
        (fun y : M => (trivializationAt E (TangentSpace I) p.1).symmL ℝ y w.1) q.1 :=
    ((LeviCivita (I := I) g).isCovariantDerivativeOnUniv).congr_of_eventuallyEq
      ((Y₁ () : Cₛ^∞⟮I; E, (TangentSpace I : M → Type _)⟯).mdifferentiableAt)
      (((Bundle.Trivialization.contMDiffOn_symmL_section (I := I)
        (trivializationAt E (TangentSpace I) p.1) w.1).contMDiffAt
        ((trivializationAt E (TangentSpace I) p.1).open_baseSet.mem_nhds h1)).mdifferentiableAt (by simp))
      Filter.univ_mem hY₁'
  have hconnY₂ : (LeviCivita (I := J) h)
        (Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯) q.2 =
      (LeviCivita (I := J) h)
        (fun y : N => (trivializationAt F (TangentSpace J) p.2).symmL ℝ y w.2) q.2 :=
    ((LeviCivita (I := J) h).isCovariantDerivativeOnUniv).congr_of_eventuallyEq
      ((Y₂ () : Cₛ^∞⟮J; F, (TangentSpace J : N → Type _)⟯).mdifferentiableAt)
      (((Bundle.Trivialization.contMDiffOn_symmL_section (I := J)
        (trivializationAt F (TangentSpace J) p.2) w.2).contMDiffAt
        ((trivializationAt F (TangentSpace J) p.2).open_baseSet.mem_nhds h2)).mdifferentiableAt (by simp))
      Filter.univ_mem hY₂'
  exact (DifferentialGeometry.trivializationAt_continuousLinearMapAt_prod_of_mem (I := I) (J := J) p hq
    (((LeviCivita (I := I) g) (Y₁ ()) q.1) v.1,
     ((LeviCivita (I := J) h) (Y₂ ()) q.2) v.2)).trans
    (by rw [hconnY₁, hconnY₂])

theorem connectionForm_leviCivita_prod (g : SmoothRiemannianMetric I M) (h : SmoothRiemannianMetric J N)
    (p : M × N) (v w : E × F) :
    (LeviCivita (I := I.prod J) (g.prod h)).connectionForm
        (trivializationAt (E × F) (TangentSpace (I.prod J)) p) p v w =
      ((LeviCivita (I := I) g).connectionForm
          (trivializationAt E (TangentSpace I) p.1) p.1 v.1 w.1,
       (LeviCivita (I := J) h).connectionForm
          (trivializationAt F (TangentSpace J) p.2) p.2 v.2 w.2) := by
  exact connectionForm_leviCivita_prod_of_mem g h p
    (FiberBundle.mem_baseSet_trivializationAt (E × F) (TangentSpace (I.prod J)) p) v w

end DifferentialGeometry.Geometry.Connection
