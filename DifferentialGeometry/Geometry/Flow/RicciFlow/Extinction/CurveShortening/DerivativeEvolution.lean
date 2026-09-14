import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TensorDerivatives
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra

noncomputable section
open Bundle Manifold Set Filter
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Geometry.Riemannian.AlongCurve
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

namespace CurveMap

theorem ds_ricci_eval (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (V W : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => V y t) x) x)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => W y t) x) x) :
    c.ds G.metric (fun y τ => G.ricciAt τ (c.lift y τ) (vec2 (V y τ) (W y τ))) x t =
      nablaRicci G t (c.lift x t) (c.unitTangent G.metric x t) (V x t) (W x t) +
      G.ricciAt t (c.lift x t) (vec2 (c.Ds G.metric V x t) (W x t)) +
      G.ricciAt t (c.lift x t) (vec2 (V x t) (c.Ds G.metric W x t)) := by
  have hh := c.ds_tensor_eval G.metric G.ricci ![V, W] x t hγ (by
    intro i
    fin_cases i
    · exact hV
    · exact hW)
  have hv (y τ : ℝ) : (fun i => ![V, W] i y τ) = vec2 (V y τ) (W y τ) := by
    funext i; fin_cases i <;> rfl
  simp only [hv, SolutionFamily.ricci_apply, Fin.sum_univ_two, Matrix.cons_val_zero,
    Matrix.cons_val_one] at hh
  have h0 : Function.update (vec2 (V x t) (W x t)) 0 (c.Ds G.metric V x t) =
      vec2 (c.Ds G.metric V x t) (W x t) := by
    funext i; fin_cases i <;> rfl
  have h1 : Function.update (vec2 (V x t) (W x t)) 1 (c.Ds G.metric W x t) =
      vec2 (V x t) (c.Ds G.metric W x t) := by
    funext i; fin_cases i <;> rfl
  rw [h0, h1] at hh
  simpa only [nablaRicci, SolutionFamily.connection, LeviCivita_eq_leviCivitaConnectionOfMetric, add_assoc] using hh

theorem ds_nablaRicci_eval (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (U V W : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x)
    (hU : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => U y t) x) x)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => V y t) x) x)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => W y t) x) x) :
    c.ds G.metric (fun y τ => nablaRicci G τ (c.lift y τ) (U y τ) (V y τ) (W y τ)) x t =
      totalNabla0SFun 3 (G.connection t) (covStep (G.metric t) 2 (G.ricci t)) (c.lift x t)
        (Fin.cons (c.unitTangent G.metric x t) (vec3 (U x t) (V x t) (W x t))) +
      nablaRicci G t (c.lift x t) (c.Ds G.metric U x t) (V x t) (W x t) +
      nablaRicci G t (c.lift x t) (U x t) (c.Ds G.metric V x t) (W x t) +
      nablaRicci G t (c.lift x t) (U x t) (V x t) (c.Ds G.metric W x t) := by
  have hh := c.ds_tensor_eval (r := 3) G.metric (fun τ => covStep (G.metric τ) 2 (G.ricci τ))
    ![U, V, W] x t hγ (by
      intro i
      fin_cases i
      · exact hU
      · exact hV
      · exact hW)
  have hv (y τ : ℝ) : (fun i => ![U, V, W] i y τ) = Fin.cons (U y τ) (vec2 (V y τ) (W y τ)) := by
    funext i; fin_cases i <;> rfl
  simp only [hv, Fin.sum_univ_three, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val_two, Matrix.head_cons, Matrix.tail_cons] at hh
  have h0 : Function.update (Fin.cons (α := fun _ : Fin 3 => TangentSpace I (c.lift x t)) (U x t) (vec2 (V x t) (W x t))) 0 (c.Ds G.metric U x t) =
      Fin.cons (c.Ds G.metric U x t) (vec2 (V x t) (W x t)) := by
    funext i; fin_cases i <;> rfl
  have h1 : Function.update (Fin.cons (α := fun _ : Fin 3 => TangentSpace I (c.lift x t)) (U x t) (vec2 (V x t) (W x t))) 1 (c.Ds G.metric V x t) =
      Fin.cons (U x t) (vec2 (c.Ds G.metric V x t) (W x t)) := by
    funext i; fin_cases i <;> rfl
  have h2 : Function.update (Fin.cons (α := fun _ : Fin 3 => TangentSpace I (c.lift x t)) (U x t) (vec2 (V x t) (W x t))) 2 (c.Ds G.metric W x t) =
      Fin.cons (U x t) (vec2 (V x t) (c.Ds G.metric W x t)) := by
    funext i; fin_cases i <;> rfl
  rw [h0, h1, h2] at hh
  have hvec : vec3 (U x t) (V x t) (W x t) = Fin.cons (U x t) (vec2 (V x t) (W x t)) := by
    funext i; fin_cases i <;> rfl
  rw [hvec]
  change c.ds G.metric (fun y τ => nablaRicci G τ (c.lift y τ) (U y τ) (V y τ) (W y τ)) x t =
    totalNabla0SFun 3 (G.connection t) (covStep (G.metric t) 2 (G.ricci t)) (c.lift x t)
      (Fin.cons (c.unitTangent G.metric x t) (Fin.cons (U x t) (vec2 (V x t) (W x t)))) +
    (nablaRicci G t (c.lift x t) (c.Ds G.metric U x t) (V x t) (W x t) +
      nablaRicci G t (c.lift x t) (U x t) (c.Ds G.metric V x t) (W x t) +
      nablaRicci G t (c.lift x t) (U x t) (V x t) (c.Ds G.metric W x t)) at hh
  exact hh.trans (by ring)

theorem ds_rm04_eval (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (U V W Z : c.Field (I := I)) (x t : ℝ)
    (hγ : MDifferentiableAt 𝓘(ℝ, ℝ) I (fun y => c.lift y t) x)
    (hU : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => U y t) x) x)
    (hV : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => V y t) x) x)
    (hW : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => W y t) x) x)
    (hZ : DifferentiableAt ℝ (chartRepAt (I := I) (fun y => c.lift y t) (fun y => Z y t) x) x) :
    c.ds G.metric (fun y τ => G.rm04At τ (c.lift y τ) (vec4 (U y τ) (V y τ) (W y τ) (Z y τ))) x t =
      totalNabla0SFun 4 (G.connection t) (G.rm04 t) (c.lift x t)
        (Fin.cons (c.unitTangent G.metric x t) (vec4 (U x t) (V x t) (W x t) (Z x t))) +
      G.rm04At t (c.lift x t) (vec4 (c.Ds G.metric U x t) (V x t) (W x t) (Z x t)) +
      G.rm04At t (c.lift x t) (vec4 (U x t) (c.Ds G.metric V x t) (W x t) (Z x t)) +
      G.rm04At t (c.lift x t) (vec4 (U x t) (V x t) (c.Ds G.metric W x t) (Z x t)) +
      G.rm04At t (c.lift x t) (vec4 (U x t) (V x t) (W x t) (c.Ds G.metric Z x t)) := by
  have hh := c.ds_tensor_eval G.metric G.rm04
    (fun i y τ => vec4 (U y τ) (V y τ) (W y τ) (Z y τ) i) x t hγ (by
      intro i
      fin_cases i
      · exact hU
      · exact hV
      · exact hW
      · exact hZ)
  rw [Fin.sum_univ_four] at hh
  have h0 : Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 0 (c.Ds G.metric U x t) =
      vec4 (c.Ds G.metric U x t) (V x t) (W x t) (Z x t) := by
    funext i; fin_cases i <;> rfl
  have h1 : Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 1 (c.Ds G.metric V x t) =
      vec4 (U x t) (c.Ds G.metric V x t) (W x t) (Z x t) := by
    funext i; fin_cases i <;> rfl
  have h2 : Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 2 (c.Ds G.metric W x t) =
      vec4 (U x t) (V x t) (c.Ds G.metric W x t) (Z x t) := by
    funext i; fin_cases i <;> rfl
  have h3 : Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 3 (c.Ds G.metric Z x t) =
      vec4 (U x t) (V x t) (W x t) (c.Ds G.metric Z x t) := by
    funext i; fin_cases i <;> rfl
  change c.ds G.metric (fun y τ => G.rm04At τ (c.lift y τ) (vec4 (U y τ) (V y τ) (W y τ) (Z y τ))) x t =
    totalNabla0SFun 4 (G.connection t) (G.rm04 t) (c.lift x t)
      (Fin.cons (c.unitTangent G.metric x t) (vec4 (U x t) (V x t) (W x t) (Z x t))) +
    (G.rm04At t (c.lift x t) (Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 0 (c.Ds G.metric U x t)) +
    G.rm04At t (c.lift x t) (Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 1 (c.Ds G.metric V x t)) +
    G.rm04At t (c.lift x t) (Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 2 (c.Ds G.metric W x t)) +
    G.rm04At t (c.lift x t) (Function.update (vec4 (U x t) (V x t) (W x t) (Z x t)) 3 (c.Ds G.metric Z x t))) at hh
  rw [h0, h1, h2, h3] at hh
  exact hh.trans (by ring)

omit [I.Boundaryless] in
theorem contDiffAt_rm04_eval (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (U V W Z : c.Field (I := I)) (x t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) x)
    (hU : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, U y t⟩ : TangentBundle I M)) x)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, V y t⟩ : TangentBundle I M)) x)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)) x)
    (hZ : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, Z y t⟩ : TangentBundle I M)) x) :
    ContDiffAt ℝ ∞ (fun y => G.rm04At t (c.lift y t) (vec4 (U y t) (V y t) (W y t) (Z y t))) x :=
  c.contDiffAt_tensor_eval (G.rm04 t) (fun i y τ => vec4 (U y τ) (V y τ) (W y τ) (Z y τ) i)
    x t hγ (by
      intro i
      fin_cases i
      · exact hU
      · exact hV
      · exact hW
      · exact hZ)

omit [I.Boundaryless] in
theorem contDiffAt_nablaRicci_eval (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (U V W : c.Field (I := I)) (x t : ℝ)
    (hγ : ContMDiffAt 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) x)
    (hU : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, U y t⟩ : TangentBundle I M)) x)
    (hV : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, V y t⟩ : TangentBundle I M)) x)
    (hW : ContMDiffAt 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)) x) :
    ContDiffAt ℝ ∞ (fun y => nablaRicci G t (c.lift y t) (U y t) (V y t) (W y t)) x :=
  c.contDiffAt_tensor_eval (r := 3) (covStep (G.metric t) 2 (G.ricci t))
    (fun i y τ => Fin.cons (α := fun _ : Fin 3 => TangentSpace I (c.lift y τ)) (U y τ) (vec2 (V y τ) (W y τ)) i)
    x t hγ (by
      intro i
      fin_cases i
      · exact hU
      · exact hV
      · exact hW)

variable [CompleteSpace E] [SigmaCompactSpace M]

omit [SigmaCompactSpace M] in
theorem ds_ricciTangent (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.ds G.metric (c.ricciTangent G) x t =
      nablaRicci G t (c.lift x t) (c.unitTangent G.metric x t)
        (c.unitTangent G.metric x t) (c.unitTangent G.metric x t) +
      G.ricciAt t (c.lift x t) (vec2 (c.curvatureVector G.metric x t) (c.unitTangent G.metric x t)) +
      G.ricciAt t (c.lift x t) (vec2 (c.unitTangent G.metric x t) (c.curvatureVector G.metric x t)) := by
  have hγ := (contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)).mdifferentiable (by simp) x
  have hT := chartRep_diff _ _ (c.unitTangent_contMDiff G.metric J hc hi t ht) x
  exact c.ds_ricci_eval G (c.unitTangent G.metric) (c.unitTangent G.metric) x t hγ hT hT

omit [SigmaCompactSpace M] in
theorem ds_ds_ricciTangent (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    let T := c.unitTangent G.metric
    let Hc := c.curvatureVector G.metric
    let V := c.Ds G.metric Hc
    c.ds G.metric (c.ds G.metric (c.ricciTangent G)) x t =
      totalNabla0SFun 3 (G.connection t) (covStep (G.metric t) 2 (G.ricci t)) (c.lift x t)
        (Fin.cons (T x t) (vec3 (T x t) (T x t) (T x t))) +
      nablaRicci G t (c.lift x t) (Hc x t) (T x t) (T x t) +
      2 * nablaRicci G t (c.lift x t) (T x t) (Hc x t) (T x t) +
      2 * nablaRicci G t (c.lift x t) (T x t) (T x t) (Hc x t) +
      G.ricciAt t (c.lift x t) (vec2 (V x t) (T x t)) +
      G.ricciAt t (c.lift x t) (vec2 (T x t) (V x t)) +
      2 * G.ricciAt t (c.lift x t) (vec2 (Hc x t) (Hc x t)) := by
  let T := c.unitTangent G.metric
  let Hc := c.curvatureVector G.metric
  let V := c.Ds G.metric Hc
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hT := c.unitTangent_contMDiff G.metric J hc hi t ht
  have hH := c.curvatureVector_contMDiff G.metric J hc hi t ht
  have hTr := chartRep_diff _ _ hT x
  have hHr := chartRep_diff _ _ hH x
  have hN : DifferentiableAt ℝ
      (fun y => nablaRicci G t (c.lift y t) (T y t) (T y t) (T y t)) x :=
    (c.contDiffAt_nablaRicci_eval G T T T x t (hγ x) (hT x) (hT x) (hT x)).differentiableAt (by simp)
  have hHT : DifferentiableAt ℝ
      (fun y => G.ricciAt t (c.lift y t) (vec2 (Hc y t) (T y t))) x :=
    (contDiffWithinAt_univ.mp (c.contDiffWithinAt_ricciTangent_slice (G.metric t) J hc Hc T x t ht hH hT)).differentiableAt (by simp)
  have hTH : DifferentiableAt ℝ
      (fun y => G.ricciAt t (c.lift y t) (vec2 (T y t) (Hc y t))) x :=
    (contDiffWithinAt_univ.mp (c.contDiffWithinAt_ricciTangent_slice (G.metric t) J hc T Hc x t ht hT hH)).differentiableAt (by simp)
  have hNH : DifferentiableAt ℝ (fun y => nablaRicci G t (c.lift y t) (T y t) (T y t) (T y t) +
      G.ricciAt t (c.lift y t) (vec2 (Hc y t) (T y t))) x := hN.add hHT
  have hfun : (fun y => c.ds G.metric (c.ricciTangent G) y t) =
      fun y => nablaRicci G t (c.lift y t) (T y t) (T y t) (T y t) +
        G.ricciAt t (c.lift y t) (vec2 (Hc y t) (T y t)) +
        G.ricciAt t (c.lift y t) (vec2 (T y t) (Hc y t)) :=
    funext (fun y => c.ds_ricciTangent G hc hi y t ht)
  have hsplit : c.ds G.metric (c.ds G.metric (c.ricciTangent G)) x t =
      c.ds G.metric (fun y τ => nablaRicci G τ (c.lift y τ) (T y τ) (T y τ) (T y τ)) x t +
      c.ds G.metric (fun y τ => G.ricciAt τ (c.lift y τ) (vec2 (Hc y τ) (T y τ))) x t +
      c.ds G.metric (fun y τ => G.ricciAt τ (c.lift y τ) (vec2 (T y τ) (Hc y τ))) x t := by
    change (c.speed G.metric x t)⁻¹ * deriv (fun y => c.ds G.metric (c.ricciTangent G) y t) x = _
    rw [hfun, deriv_fun_add hNH hTH, deriv_fun_add hN hHT]
    dsimp only [CurveMap.ds]
    ring
  rw [hsplit, c.ds_nablaRicci_eval G T T T x t ((hγ x).mdifferentiableAt (by simp)) hTr hTr hTr,
    c.ds_ricci_eval G Hc T x t ((hγ x).mdifferentiableAt (by simp)) hHr hTr,
    c.ds_ricci_eval G T Hc x t ((hγ x).mdifferentiableAt (by simp)) hTr hHr]
  change _ + (_ + _ + _) + (_ + _ + _) = _
  dsimp only [T, Hc, V, CurveMap.curvatureVector]
  ring

theorem inner_Ds_Ds_curvatureVector_unitTangent
    (c : CurveMap M) (g : ℝ → SmoothRiemannianMetric I M) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    (g t).inner (c.lift x t) (c.Ds g (c.Ds g (c.curvatureVector g)) x t) (c.unitTangent g x t) =
      -3 * (g t).inner (c.lift x t) (c.Ds g (c.curvatureVector g) x t) (c.curvatureVector g x t) := by
  have hH := c.curvatureVector_contMDiff g J hc hi t ht
  have hT := c.unitTangent_contMDiff g J hc hi t ht
  have hD : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, c.Ds g (c.curvatureVector g) y t⟩ : TangentBundle I M)) := by
    have hs := (c.speed_contDiff g J hc hi t ht).inv (fun y => (c.speed_pos g hi y t ht).ne')
    exact hs.contMDiff.smul_bundle (fun y =>
      contMDiffAt_covDerivAlong (g t) (m := ⊤) (n := ⊤) (by simp) (hH y))
  have hh := c.ds_inner g J hc (c.Ds g (c.curvatureVector g)) (c.unitTangent g) x t ht hD hT
  have heq : (fun y => (g t).inner (c.lift y t) (c.Ds g (c.curvatureVector g) y t)
      (c.unitTangent g y t)) = fun y => -c.curvatureSq g y t :=
    funext (fun y => (tangent_curvature_geometry g c J hc hi y t ht).2.2)
  have hleft : c.ds g (fun y τ => (g τ).inner (c.lift y τ) (c.Ds g (c.curvatureVector g) y τ)
      (c.unitTangent g y τ)) x t = -c.ds g (c.curvatureSq g) x t := by
    dsimp only [CurveMap.ds]
    rw [heq, deriv.fun_neg, mul_neg]
  rw [hleft, c.ds_curvatureSq_eq g J hc hi x t ht] at hh
  change - (2 * (g t).inner (c.lift x t) (c.Ds g (c.curvatureVector g) x t)
      (c.curvatureVector g x t)) =
    (g t).inner (c.lift x t) (c.Ds g (c.Ds g (c.curvatureVector g)) x t) (c.unitTangent g x t) +
    (g t).inner (c.lift x t) (c.Ds g (c.curvatureVector g) x t) (c.curvatureVector g x t) at hh
  linarith

variable {D : RealTimeInterval} {a b s u : ℝ}

theorem curvatureDerivative_evolution
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u) :
    let g := B.family.metric
    let T := c.unitTangent g
    let Hc := c.curvatureVector g
    let V := c.Ds g Hc
    let W := c.Ds g V
    let S : c.Field (I := I) → ℝ → ℝ → ℝ := fun Z y τ =>
      B.family.rm04At τ (c.lift y τ) (vec4 (Hc y τ) (T y τ) (T y τ) (Z y τ)) -
      2 * nablaRicci B.family τ (c.lift y τ) (T y τ) (T y τ) (Z y τ) +
      nablaRicci B.family τ (c.lift y τ) (Z y τ) (T y τ) (T y τ)
    derivWithin (c.normSq g V x) (Icc s u) t - c.ds g (c.ds g (c.normSq g V)) x t =
      -2 * c.normSq g W x t - 2 * c.curvatureSq g x t * c.ds g (c.ds g (c.q B.family)) x t +
      6 * c.ds g (c.q B.family) x t * (g t).inner (c.lift x t) (V x t) (Hc x t) +
      6 * c.q B.family x t * c.normSq g V x t + 2 * c.ds g (S V) x t - 2 * S W x t +
      2 * B.family.rm04At t (c.lift x t) (vec4 (Hc x t) (T x t) (Hc x t) (V x t)) -
      2 * nablaRicci B.family t (c.lift x t) (T x t) (Hc x t) (V x t) -
      2 * nablaRicci B.family t (c.lift x t) (Hc x t) (T x t) (V x t) +
      2 * nablaRicci B.family t (c.lift x t) (V x t) (T x t) (Hc x t) -
      2 * B.family.ricciAt t (c.lift x t) (vec2 (V x t) (V x t)) := by
  let g := B.family.metric
  let T := c.unitTangent g
  let Hc := c.curvatureVector g
  let V := c.Ds g Hc
  let W := c.Ds g V
  let S : c.Field (I := I) → ℝ → ℝ → ℝ := fun Z y τ =>
    B.family.rm04At τ (c.lift y τ) (vec4 (Hc y τ) (T y τ) (T y τ) (Z y τ)) -
    2 * nablaRicci B.family τ (c.lift y τ) (T y τ) (T y τ) (Z y τ) +
    nablaRicci B.family τ (c.lift y τ) (Z y τ) (T y τ) (T y τ)
  have hJ : Icc s u ⊆ D.regular := fun r hr => B.regular (hwindow hr)
  have hT := Field.smoothOn_unitTangent g B.smooth hJ c hc.smooth hc.immersed
  have hH := Field.smoothOn_curvatureVector g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed
  have hV := Field.smoothOn_Ds g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed Hc hH
  have hW := Field.smoothOn_Ds g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth hc.immersed V hV
  have hDt := Field.smoothOn_Dt g B.smooth hJ (uniqueDiffOn_Icc hsu) c hc.smooth Hc hH
  have hspace (Z : c.Field (I := I)) (hZ : Z.SmoothOn (I := I) (Icc s u)) :
      ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, Z y t⟩ : TangentBundle I M)) :=
    fun y => contMDiffWithinAt_univ.mp
      (CurveShortening.Field.space_slice_contMDiffWithinAt c _ Z hZ y t ht)
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn _ hc.smooth t ht)
  have hS (Z : c.Field (I := I)) (hZ : Z.SmoothOn (I := I) (Icc s u)) (y : ℝ) :
      ContDiffAt ℝ ∞ (fun z => S Z z t) y :=
    ((c.contDiffAt_rm04_eval B.family Hc T T Z y t (hγ y)
      (hspace Hc hH y) (hspace T hT y) (hspace T hT y) (hspace Z hZ y)).sub
      (contDiffAt_const.mul (c.contDiffAt_nablaRicci_eval B.family T T Z y t (hγ y)
        (hspace T hT y) (hspace T hT y) (hspace Z hZ y)))).add
      (c.contDiffAt_nablaRicci_eval B.family Z T T y t (hγ y)
        (hspace Z hZ y) (hspace T hT y) (hspace T hT y))
  have hq (y : ℝ) : ContDiffAt ℝ ∞ (fun z => c.q B.family z t) y :=
    ((c.curvatureSq_contDiff g (Icc s u) hc.smooth hc.immersed t ht).contDiffAt (x := y)).add
      (contDiffWithinAt_univ.mp (c.contDiffWithinAt_ricciTangent_slice (g t) (Icc s u)
        hc.smooth T T y t ht (hspace T hT) (hspace T hT)))
  have hdq : DifferentiableAt ℝ (fun y => c.ds g (c.q B.family) y t) x :=
    (((c.speed_contDiff g (Icc s u) hc.smooth hc.immersed t ht).contDiffAt.inv
      (c.speed_pos g hc.immersed x t ht).ne').mul
      ((hq x).derivWithin (m := ∞) (by simp))).differentiableAt (by simp)
  have hqdiff := (hq x).differentiableAt (by simp)
  have hkdiff := (c.curvatureSq_contDiff g (Icc s u) hc.smooth hc.immersed t ht).differentiable (by simp) x
  have hpair (Z : c.Field (I := I)) (y : ℝ) :
      (g t).inner (c.lift y t) (c.Dt g (Icc s u) Hc y t) (Z y t) =
        (g t).inner (c.lift y t) (W y t) (Z y t) +
        c.ds g (c.q B.family) y t * (g t).inner (c.lift y t) (T y t) (Z y t) +
        2 * c.q B.family y t * (g t).inner (c.lift y t) (Hc y t) (Z y t) + S Z y t := by
    rw [c.Dt_curvatureVector B hsu hwindow hc y t ht]
    simp only [map_add, add_apply, map_smul, smul_apply, smul_eq_mul]
    rw [inner_riemannVector_eq_rm04 B.family, rfs_csf_connection B t (hwindow ht)]
    dsimp only [S]
    ring
  have hTV (y : ℝ) : (g t).inner (c.lift y t) (T y t) (V y t) = -c.curvatureSq g y t := by
    rw [(g t).symm]
    exact (tangent_curvature_geometry g c (Icc s u) hc.smooth hc.immersed y t ht).2.2
  have hTW : (g t).inner (c.lift x t) (T x t) (W x t) =
      -3 * (g t).inner (c.lift x t) (V x t) (Hc x t) := by
    rw [(g t).symm]
    exact c.inner_Ds_Ds_curvatureVector_unitTangent g hc.smooth hc.immersed x t ht
  have heq : (fun y => (g t).inner (c.lift y t) (c.Dt g (Icc s u) Hc y t) (V y t)) =
      fun y => (g t).inner (c.lift y t) (W y t) (V y t) -
        c.ds g (c.q B.family) y t * c.curvatureSq g y t +
        2 * (c.q B.family y t * (g t).inner (c.lift y t) (Hc y t) (V y t)) + S V y t := by
    funext y
    rw [hpair V y, hTV y]
    ring
  have hWV := c.differentiableAt_inner_slice g (Icc s u) hc.smooth W V x t ht (hspace W hW) (hspace V hV)
  have hHV := c.differentiableAt_inner_slice g (Icc s u) hc.smooth Hc V x t ht (hspace Hc hH) (hspace V hV)
  have hpdk : DifferentiableAt ℝ (fun y => c.ds g (c.q B.family) y t * c.curvatureSq g y t) x :=
    hdq.mul hkdiff
  have hpq : DifferentiableAt ℝ
      (fun y => c.q B.family y t * (g t).inner (c.lift y t) (Hc y t) (V y t)) x := hqdiff.mul hHV
  have hp2 : DifferentiableAt ℝ
      (fun y => 2 * (c.q B.family y t * (g t).inner (c.lift y t) (Hc y t) (V y t))) x := hpq.const_mul 2
  have hminus : DifferentiableAt ℝ (fun y => (g t).inner (c.lift y t) (W y t) (V y t) -
      c.ds g (c.q B.family) y t * c.curvatureSq g y t) x := hWV.sub hpdk
  have hcomb : DifferentiableAt ℝ (fun y => (g t).inner (c.lift y t) (W y t) (V y t) -
      c.ds g (c.q B.family) y t * c.curvatureSq g y t +
      2 * (c.q B.family y t * (g t).inner (c.lift y t) (Hc y t) (V y t))) x := hminus.add hp2
  have hsplit :
      c.ds g (fun y τ => (g τ).inner (c.lift y τ) (c.Dt g (Icc s u) Hc y τ) (V y τ)) x t =
      c.ds g (fun y τ => (g τ).inner (c.lift y τ) (W y τ) (V y τ)) x t -
      (c.ds g (c.ds g (c.q B.family)) x t * c.curvatureSq g x t +
        c.ds g (c.q B.family) x t * c.ds g (c.curvatureSq g) x t) +
      2 * (c.ds g (c.q B.family) x t * (g t).inner (c.lift x t) (Hc x t) (V x t) +
        c.q B.family x t * c.ds g (fun y τ => (g τ).inner (c.lift y τ) (Hc y τ) (V y τ)) x t) +
      c.ds g (S V) x t := by
    dsimp only [CurveMap.ds]
    rw [heq, deriv_fun_add hcomb ((hS V hV x).differentiableAt (by simp)),
      deriv_fun_add hminus hp2, deriv_fun_sub hWV hpdk, deriv_fun_mul hdq hkdiff,
      deriv_const_mul 2 hpq, deriv_fun_mul hqdiff hHV]
    dsimp only [CurveMap.ds]
    ring
  have hDsDt := c.ds_inner g (Icc s u) hc.smooth (c.Dt g (Icc s u) Hc) V x t ht (hspace _ hDt) (hspace V hV)
  have hDsWV := c.ds_inner g (Icc s u) hc.smooth W V x t ht (hspace W hW) (hspace V hV)
  have hDsHV := c.ds_inner g (Icc s u) hc.smooth Hc V x t ht (hspace Hc hH) (hspace V hV)
  rw [hDsDt, hDsWV, hDsHV, c.ds_curvatureSq_eq g (Icc s u) hc.smooth hc.immersed x t ht] at hsplit
  have hPW := hpair W x
  rw [hTW] at hPW
  have hVH : (g t).inner (c.lift x t) (Hc x t) (V x t) =
      (g t).inner (c.lift x t) (V x t) (Hc x t) := (g t).symm _ _ _
  rw [hVH] at hsplit
  have hcore : (g t).inner (c.lift x t) (c.Ds g (c.Dt g (Icc s u) Hc) x t) (V x t) -
      (g t).inner (c.lift x t) (c.Ds g W x t) (V x t) =
      -c.curvatureSq g x t * c.ds g (c.ds g (c.q B.family)) x t +
      3 * c.ds g (c.q B.family) x t * (g t).inner (c.lift x t) (V x t) (Hc x t) +
      2 * c.q B.family x t * c.normSq g V x t + c.ds g (S V) x t - S W x t := by
    change _ + (g t).inner (c.lift x t) (c.Dt g (Icc s u) Hc x t) (W x t) =
      _ + c.normSq g W x t - _ + 2 * (_ + c.q B.family x t *
        (c.normSq g V x t + (g t).inner (c.lift x t) (Hc x t) (W x t))) + _ at hsplit
    change (g t).inner (c.lift x t) (c.Dt g (Icc s u) Hc x t) (W x t) =
      c.normSq g W x t + _ + _ + _ at hPW
    nlinarith [hsplit, hPW]
  have hcomm := c.Dt_Ds_commutator B hsu hwindow hc Hc hH x t ht
  have hvpos := c.speed_pos g hc.immersed x t ht
  have hX : c.X x t = c.speed g x t • T x t := by
    dsimp only [T, unitTangent]
    rw [smul_smul, mul_inv_cancel₀ hvpos.ne', one_smul]
  have hR : riemannVector B.family t (c.lift x t) (c.velocity (Icc s u) x t) (c.X x t) (Hc x t) =
      c.speed g x t • riemannVector B.family t (c.lift x t) (Hc x t) (T x t) (Hc x t) := by
    rw [hc.equation x t ht, hX, riemannVector_eq_riemannOp, riemannVector_eq_riemannOp, map_smul, smul_apply]
  have hP : connectionVariation B.family (Icc s u) t (c.lift x t) (c.X x t) (Hc x t) =
      c.speed g x t • connectionVariation B.family (Icc a b) t (c.lift x t) (T x t) (Hc x t) := by
    rw [connectionVariation_congr_set B hsu hwindow t ht, hX,
      (connectionVariation_tensor B t (hwindow ht) (c.lift x t)).2.2]
  rw [hR, hP, ← smul_add, smul_smul, inv_mul_cancel₀ hvpos.ne', one_smul] at hcomm
  have hn := c.normSq_evolution B hsu hwindow hc.smooth hc.immersed V hV x t ht
  rw [hcomm] at hn
  simp only [map_sub, sub_apply, map_add, add_apply, map_smul, smul_apply, smul_eq_mul] at hn
  rw [inner_riemannVector_eq_rm04 B.family, rfs_csf_connection B t (hwindow ht)] at hn
  have hvv : (g t).inner (c.lift x t) (V x t) (V x t) = c.normSq g V x t := rfl
  change _ = 2 * (_ + c.q B.family x t * (g t).inner (c.lift x t) (V x t) (V x t) +
    (_ + _) - _) - _ - _ at hn
  rw [hvv] at hn
  dsimp only
  nlinarith [hcore, hn]

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
