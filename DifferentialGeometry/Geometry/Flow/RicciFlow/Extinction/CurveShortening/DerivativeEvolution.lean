import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.Evolution
import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.TensorDerivatives
import DifferentialGeometry.Geometry.Metric.Convergence.CovariantDerivative.Algebra
import DifferentialGeometry.Geometry.Metric.Coordinates.InnerExpansion

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

omit [SigmaCompactSpace M] in
theorem ds_curvature_forcing_pairing (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (Z : c.Field (I := I)) (x t : ℝ) (ht : t ∈ J)
    (hZ : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Z y t⟩ : TangentBundle I M))) :
    let T := c.unitTangent G.metric
    let Hc := c.curvatureVector G.metric
    let V := c.Ds G.metric Hc
    let S : c.Field (I := I) → ℝ → ℝ → ℝ := fun U y τ =>
      G.rm04At τ (c.lift y τ) (vec4 (Hc y τ) (T y τ) (T y τ) (U y τ)) -
      2 * nablaRicci G τ (c.lift y τ) (T y τ) (T y τ) (U y τ) +
      nablaRicci G τ (c.lift y τ) (U y τ) (T y τ) (T y τ)
    c.ds G.metric (S Z) x t - S (c.Ds G.metric Z) x t =
      totalNabla0SFun 4 (G.connection t) (G.rm04 t) (c.lift x t)
        (Fin.cons (T x t) (vec4 (Hc x t) (T x t) (T x t) (Z x t))) +
      G.rm04At t (c.lift x t) (vec4 (V x t) (T x t) (T x t) (Z x t)) +
      G.rm04At t (c.lift x t) (vec4 (Hc x t) (Hc x t) (T x t) (Z x t)) +
      G.rm04At t (c.lift x t) (vec4 (Hc x t) (T x t) (Hc x t) (Z x t)) -
      2 * totalNabla0SFun 3 (G.connection t) (covStep (G.metric t) 2 (G.ricci t)) (c.lift x t)
        (Fin.cons (T x t) (vec3 (T x t) (T x t) (Z x t))) +
      totalNabla0SFun 3 (G.connection t) (covStep (G.metric t) 2 (G.ricci t)) (c.lift x t)
        (Fin.cons (T x t) (vec3 (Z x t) (T x t) (T x t))) -
      2 * nablaRicci G t (c.lift x t) (Hc x t) (T x t) (Z x t) -
      2 * nablaRicci G t (c.lift x t) (T x t) (Hc x t) (Z x t) +
      nablaRicci G t (c.lift x t) (Z x t) (Hc x t) (T x t) +
      nablaRicci G t (c.lift x t) (Z x t) (T x t) (Hc x t) := by
  let T := c.unitTangent G.metric
  let Hc := c.curvatureVector G.metric
  have hγ : ContMDiff 𝓘(ℝ, ℝ) I ∞ (fun y => c.lift y t) :=
    contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hT := c.unitTangent_contMDiff G.metric J hc hi t ht
  have hH := c.curvatureVector_contMDiff G.metric J hc hi t ht
  have hTr := chartRep_diff _ _ hT x
  have hHr := chartRep_diff _ _ hH x
  have hZr := chartRep_diff _ _ hZ x
  have hR : DifferentiableAt ℝ
      (fun y => G.rm04At t (c.lift y t) (vec4 (Hc y t) (T y t) (T y t) (Z y t))) x :=
    (c.contDiffAt_rm04_eval G Hc T T Z x t (hγ x) (hH x) (hT x) (hT x) (hZ x)).differentiableAt (by simp)
  have hN : DifferentiableAt ℝ
      (fun y => nablaRicci G t (c.lift y t) (T y t) (T y t) (Z y t)) x :=
    (c.contDiffAt_nablaRicci_eval G T T Z x t (hγ x) (hT x) (hT x) (hZ x)).differentiableAt (by simp)
  have hN' : DifferentiableAt ℝ
      (fun y => nablaRicci G t (c.lift y t) (Z y t) (T y t) (T y t)) x :=
    (c.contDiffAt_nablaRicci_eval G Z T T x t (hγ x) (hZ x) (hT x) (hT x)).differentiableAt (by simp)
  have h2N : DifferentiableAt ℝ
      (fun y => 2 * nablaRicci G t (c.lift y t) (T y t) (T y t) (Z y t)) x := hN.const_mul 2
  have hRN : DifferentiableAt ℝ
      (fun y => G.rm04At t (c.lift y t) (vec4 (Hc y t) (T y t) (T y t) (Z y t)) -
        2 * nablaRicci G t (c.lift y t) (T y t) (T y t) (Z y t)) x := hR.sub h2N
  have hsplit :
      c.ds G.metric (fun y τ => G.rm04At τ (c.lift y τ) (vec4 (Hc y τ) (T y τ) (T y τ) (Z y τ)) -
        2 * nablaRicci G τ (c.lift y τ) (T y τ) (T y τ) (Z y τ) +
        nablaRicci G τ (c.lift y τ) (Z y τ) (T y τ) (T y τ)) x t =
      c.ds G.metric (fun y τ => G.rm04At τ (c.lift y τ) (vec4 (Hc y τ) (T y τ) (T y τ) (Z y τ))) x t -
      2 * c.ds G.metric (fun y τ => nablaRicci G τ (c.lift y τ) (T y τ) (T y τ) (Z y τ)) x t +
      c.ds G.metric (fun y τ => nablaRicci G τ (c.lift y τ) (Z y τ) (T y τ) (T y τ)) x t := by
    dsimp only [CurveMap.ds]
    rw [deriv_fun_add hRN hN', deriv_fun_sub hR h2N, deriv_const_mul 2 hN]
    ring
  dsimp only
  rw [hsplit, c.ds_rm04_eval G Hc T T Z x t ((hγ x).mdifferentiableAt (by simp)) hHr hTr hTr hZr,
    c.ds_nablaRicci_eval G T T Z x t ((hγ x).mdifferentiableAt (by simp)) hTr hTr hZr,
    c.ds_nablaRicci_eval G Z T T x t ((hγ x).mdifferentiableAt (by simp)) hZr hTr hTr]
  change _ = _
  dsimp only [T, Hc, CurveMap.curvatureVector]
  ring

omit [SigmaCompactSpace M] in
theorem ds_q (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.ds G.metric (c.q G) x t =
      2 * (G.metric t).inner (c.lift x t) (c.Ds G.metric (c.curvatureVector G.metric) x t)
        (c.curvatureVector G.metric x t) + c.ds G.metric (c.ricciTangent G) x t := by
  have hT := c.unitTangent_contMDiff G.metric J hc hi t ht
  have hk := (c.curvatureSq_contDiff G.metric J hc hi t ht).differentiable (by simp) x
  have hρ := (contDiffWithinAt_univ.mp (c.contDiffWithinAt_ricciTangent_slice (G.metric t) J hc
    (c.unitTangent G.metric) (c.unitTangent G.metric) x t ht hT hT)).differentiableAt (by simp)
  change c.ds G.metric (fun y τ => c.curvatureSq G.metric y τ + c.ricciTangent G y τ) x t = _
  rw [c.ds_add G.metric _ _ x t hk hρ, c.ds_curvatureSq_eq G.metric J hc hi x t ht]

omit [SigmaCompactSpace M] in
theorem ds_ds_q (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    {J : Set ℝ} (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (x t : ℝ) (ht : t ∈ J) :
    c.ds G.metric (c.ds G.metric (c.q G)) x t =
      2 * (G.metric t).inner (c.lift x t) (c.Ds G.metric (c.Ds G.metric (c.curvatureVector G.metric)) x t)
        (c.curvatureVector G.metric x t) + 2 * c.normSq G.metric (c.Ds G.metric (c.curvatureVector G.metric)) x t +
      c.ds G.metric (c.ds G.metric (c.ricciTangent G)) x t := by
  let T := c.unitTangent G.metric
  let Hc := c.curvatureVector G.metric
  let V := c.Ds G.metric Hc
  have hT := c.unitTangent_contMDiff G.metric J hc hi t ht
  have hH := c.curvatureVector_contMDiff G.metric J hc hi t ht
  have hV : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, V y t⟩ : TangentBundle I M)) := by
    have hs := (c.speed_contDiff G.metric J hc hi t ht).inv (fun y => (c.speed_pos G.metric hi y t ht).ne')
    exact hs.contMDiff.smul_bundle (fun y =>
      contMDiffAt_covDerivAlong (G.metric t) (m := ⊤) (n := ⊤) (by simp) (hH y))
  have hpair := c.differentiableAt_inner_slice G.metric J hc V Hc x t ht hV hH
  have h2pair : DifferentiableAt ℝ
      (fun y => 2 * (G.metric t).inner (c.lift y t) (V y t) (Hc y t)) x := hpair.const_mul 2
  have hρ : ContDiffAt ℝ ∞ (fun y => c.ricciTangent G y t) x :=
    contDiffWithinAt_univ.mp (c.contDiffWithinAt_ricciTangent_slice (G.metric t) J hc T T x t ht hT hT)
  have hdρ : DifferentiableAt ℝ (fun y => c.ds G.metric (c.ricciTangent G) y t) x :=
    (((c.speed_contDiff G.metric J hc hi t ht).contDiffAt.inv (c.speed_pos G.metric hi x t ht).ne').mul
      (hρ.derivWithin (m := ∞) (by simp))).differentiableAt (by simp)
  have heq : (fun y => c.ds G.metric (c.q G) y t) =
      fun y => 2 * (G.metric t).inner (c.lift y t) (V y t) (Hc y t) +
        c.ds G.metric (c.ricciTangent G) y t := funext (fun y => c.ds_q G hc hi y t ht)
  have hsplit : c.ds G.metric (c.ds G.metric (c.q G)) x t =
      2 * c.ds G.metric (fun y τ => (G.metric τ).inner (c.lift y τ) (V y τ) (Hc y τ)) x t +
      c.ds G.metric (c.ds G.metric (c.ricciTangent G)) x t := by
    change (c.speed G.metric x t)⁻¹ * deriv (fun y => c.ds G.metric (c.q G) y t) x = _
    rw [heq, deriv_fun_add h2pair hdρ, deriv_const_mul 2 hpair]
    dsimp only [CurveMap.ds]
    ring
  rw [hsplit, c.ds_inner G.metric J hc V Hc x t ht hV hH]
  change 2 * (_ + c.normSq G.metric V x t) + _ = _
  ring

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

theorem curvatureDerivative_evolution_le_of_tensor_bounds
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u)) (x t : ℝ) (ht : t ∈ Icc s u)
    (C Λ : ℝ) (hC : B.C ≤ C) (hΛ : 1 ≤ Λ) (hk : c.curvatureSq B.family.metric x t ≤ Λ)
    (hDR : normSq0S (B.family.metric t) (c.lift x t) 5
      (totalNabla0SFun 4 (B.family.connection t) (B.family.rm04 t) (c.lift x t)) ≤ C ^ 2)
    (hDDRic : normSq0S (B.family.metric t) (c.lift x t) 4
      (totalNabla0SFun 3 (B.family.connection t)
        (covStep (B.family.metric t) 2 (B.family.ricci t)) (c.lift x t)) ≤ C ^ 2) :
    let g := B.family.metric
    let V := c.Ds g (c.curvatureVector g)
    derivWithin (c.normSq g V x) (Icc s u) t - c.ds g (c.ds g (c.normSq g V)) x t ≤
      -c.normSq g (c.Ds g V) x t + 64 * (1 + C) * Λ * c.normSq g V x t + 64 * (1 + C) * Λ ^ 2 := by
  let G := B.family
  let g := G.metric
  let p := c.lift x t
  let T := c.unitTangent g
  let Hc := c.curvatureVector g
  let V := c.Ds g Hc
  let W := c.Ds g V
  let n : TangentSpace I p → ℝ := fun U => Real.sqrt ((g t).inner p U U)
  let k := n (Hc x t)
  let z := n (V x t)
  let w := n (W x t)
  have hC0 : 0 ≤ C := by
    dsimp only [RicciBackground.C] at hC
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hB0 : B.B₀ ≤ C := by
    dsimp only [RicciBackground.C] at hC
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hB1 : B.B₁ ≤ C := by
    dsimp only [RicciBackground.C] at hC
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hB2 : B.B₂ ≤ C := by
    dsimp only [RicciBackground.C] at hC
    linarith [B.B₀_nonneg, B.B₁_nonneg, B.B₂_nonneg]
  have hn (U : TangentSpace I p) : 0 ≤ n U := Real.sqrt_nonneg _
  have hnsq (U : TangentSpace I p) : n U ^ 2 = (g t).inner p U U :=
    Real.sq_sqrt (DifferentialGeometry.metric_inner_self_nonneg (g t) p U)
  have hnT : n (T x t) = 1 := by
    dsimp only [n, p, T]
    rw [(tangent_curvature_geometry g c (Icc s u) hc.smooth hc.immersed x t ht).1, Real.sqrt_one]
  have hbound (r : ℕ) (A : Tensor0SSpace r I p) (hA : normSq0S (g t) p r A ≤ C ^ 2)
      (U : Fin r → TangentSpace I p) : |A U| ≤ C * ∏ i, n (U i) :=
    (abs_apply_le_norm0S (g t) p r A U).trans
      (mul_le_mul_of_nonneg_right (Real.sqrt_le_iff.mpr ⟨hC0, hA⟩)
        (Finset.prod_nonneg (fun i _ => hn (U i))))
  have hRic (U Z : TangentSpace I p) : |G.ricciAt t p (vec2 U Z)| ≤ C * n U * n Z := by
    have hh := hbound 2 (G.ricciAt t p)
      ((B.ricci_bound t (hwindow ht) p).trans (pow_le_pow_left₀ B.B₀_nonneg hB0 2)) (vec2 U Z)
    simpa [Fin.prod_univ_two, vec2, mul_assoc] using hh
  have hR (U Z Y X : TangentSpace I p) : |G.rm04At t p (vec4 U Z Y X)| ≤ C * n U * n Z * n Y * n X := by
    have hh := hbound 4 (G.rm04At t p)
      ((B.riemann_bound t (hwindow ht) p).trans (pow_le_pow_left₀ B.B₁_nonneg hB1 2)) (vec4 U Z Y X)
    simpa [Fin.prod_univ_four, vec4, mul_assoc] using hh
  have hN (U Z Y : TangentSpace I p) : |nablaRicci G t p U Z Y| ≤ C * n U * n Z * n Y := by
    have hh := hbound 3 (totalNabla0SFun 2 (G.connection t) (G.ricci t) p)
      ((B.nablaRicci_bound t (hwindow ht) p).trans (pow_le_pow_left₀ B.B₂_nonneg hB2 2)) (vec3 U Z Y)
    rw [nablaRicci_vec3]
    simpa [Fin.prod_univ_three, vec3, mul_assoc] using hh
  have hN2 (U Z Y X : TangentSpace I p) :
      |totalNabla0SFun 3 (G.connection t) (covStep (g t) 2 (G.ricci t)) p (Fin.cons U (vec3 Z Y X))| ≤
        C * n U * n Z * n Y * n X := by
    have hh := hbound 4 _ hDDRic (Fin.cons U (vec3 Z Y X))
    simpa [Fin.prod_univ_succ, vec3, mul_assoc] using hh
  have hR1 (U Z Y X A : TangentSpace I p) :
      |totalNabla0SFun 4 (G.connection t) (G.rm04 t) p (Fin.cons U (vec4 Z Y X A))| ≤
        C * n U * n Z * n Y * n X * n A := by
    have hh := hbound 5 _ hDR (Fin.cons U (vec4 Z Y X A))
    simpa [Fin.prod_univ_succ, vec4, mul_assoc] using hh
  have hρ : |c.ricciTangent G x t| ≤ C := by
    change |G.ricciAt t p (vec2 (T x t) (T x t))| ≤ C
    simpa only [hnT, mul_one] using hRic (T x t) (T x t)
  have hdρ : |c.ds g (c.ricciTangent G) x t| ≤ C + 2 * C * k := by
    rw [c.ds_ricciTangent G hc.smooth hc.immersed x t ht]
    have h1 := hN (T x t) (T x t) (T x t)
    have h2 := hRic (Hc x t) (T x t)
    have h3 := hRic (T x t) (Hc x t)
    simp only [hnT, mul_one] at h1 h2 h3
    rcases abs_le.mp h1 with ⟨h1l, h1u⟩
    rcases abs_le.mp h2 with ⟨h2l, h2u⟩
    rcases abs_le.mp h3 with ⟨h3l, h3u⟩
    apply abs_le.mpr
    constructor <;> linarith only [h1l, h1u, h2l, h2u, h3l, h3u]
  have hddρ : |c.ds g (c.ds g (c.ricciTangent G)) x t| ≤ C + 5 * C * k + 2 * C * z + 2 * C * k ^ 2 := by
    rw [c.ds_ds_ricciTangent G hc.smooth hc.immersed x t ht]
    have h1 := hN2 (T x t) (T x t) (T x t) (T x t)
    have h2 := hN (Hc x t) (T x t) (T x t)
    have h3 := hN (T x t) (Hc x t) (T x t)
    have h4 := hN (T x t) (T x t) (Hc x t)
    have h5 := hRic (V x t) (T x t)
    have h6 := hRic (T x t) (V x t)
    have h7 := hRic (Hc x t) (Hc x t)
    simp only [hnT, mul_one] at h1 h2 h3 h4 h5 h6 h7
    rcases abs_le.mp h1 with ⟨h1l, h1u⟩
    rcases abs_le.mp h2 with ⟨h2l, h2u⟩
    rcases abs_le.mp h3 with ⟨h3l, h3u⟩
    rcases abs_le.mp h4 with ⟨h4l, h4u⟩
    rcases abs_le.mp h5 with ⟨h5l, h5u⟩
    rcases abs_le.mp h6 with ⟨h6l, h6u⟩
    rcases abs_le.mp h7 with ⟨h7l, h7u⟩
    apply abs_le.mpr
    constructor <;> linarith only [h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u, h6l, h6u, h7l, h7u]
  let S : c.Field (I := I) → ℝ → ℝ → ℝ := fun Z y τ =>
    G.rm04At τ (c.lift y τ) (vec4 (Hc y τ) (T y τ) (T y τ) (Z y τ)) -
    2 * nablaRicci G τ (c.lift y τ) (T y τ) (T y τ) (Z y τ) +
    nablaRicci G τ (c.lift y τ) (Z y τ) (T y τ) (T y τ)
  have hVs := c.Ds_curvatureVector_slice_contMDiff g B.smooth
    (fun r hr => B.regular (hwindow hr)) (uniqueDiffOn_Icc hsu) hc.smooth hc.immersed t ht
  have hDS : |c.ds g (S V) x t - S W x t| ≤
      7 * C * k * z + C * z ^ 2 + 2 * C * k ^ 2 * z + 3 * C * z := by
    have heq := c.ds_curvature_forcing_pairing G hc.smooth hc.immersed V x t ht hVs
    change c.ds g (S V) x t - S W x t = _ at heq
    rw [heq]
    have h1 := hR1 (T x t) (Hc x t) (T x t) (T x t) (V x t)
    have h2 := hR (V x t) (T x t) (T x t) (V x t)
    have h3 := hR (Hc x t) (Hc x t) (T x t) (V x t)
    have h4 := hR (Hc x t) (T x t) (Hc x t) (V x t)
    have h5 := hN2 (T x t) (T x t) (T x t) (V x t)
    have h6 := hN2 (T x t) (V x t) (T x t) (T x t)
    have h7 := hN (Hc x t) (T x t) (V x t)
    have h8 := hN (T x t) (Hc x t) (V x t)
    have h9 := hN (V x t) (Hc x t) (T x t)
    have h10 := hN (V x t) (T x t) (Hc x t)
    simp only [hnT, mul_one] at h1 h2 h3 h4 h5 h6 h7 h8 h9 h10
    rcases abs_le.mp h1 with ⟨h1l, h1u⟩
    rcases abs_le.mp h2 with ⟨h2l, h2u⟩
    rcases abs_le.mp h3 with ⟨h3l, h3u⟩
    rcases abs_le.mp h4 with ⟨h4l, h4u⟩
    rcases abs_le.mp h5 with ⟨h5l, h5u⟩
    rcases abs_le.mp h6 with ⟨h6l, h6u⟩
    rcases abs_le.mp h7 with ⟨h7l, h7u⟩
    rcases abs_le.mp h8 with ⟨h8l, h8u⟩
    rcases abs_le.mp h9 with ⟨h9l, h9u⟩
    rcases abs_le.mp h10 with ⟨h10l, h10u⟩
    apply abs_le.mpr
    constructor <;> linarith only [h1l, h1u, h2l, h2u, h3l, h3u, h4l, h4u, h5l, h5u, h6l, h6u, h7l, h7u, h8l, h8u, h9l, h9u, h10l, h10u]
  let P := (g t).inner p (V x t) (Hc x t)
  let Q := (g t).inner p (W x t) (Hc x t)
  have hk0 : 0 ≤ k := hn _
  have hz0 : 0 ≤ z := hn _
  have hΛ0 : 0 ≤ Λ := le_trans zero_le_one hΛ
  have hk2 : c.curvatureSq g x t = k ^ 2 := (hnsq _).symm
  have hz2 : c.normSq g V x t = z ^ 2 := (hnsq _).symm
  have hw2 : c.normSq g W x t = w ^ 2 := (hnsq _).symm
  have hkΛ : k ^ 2 ≤ Λ := by rw [← hk2]; exact hk
  have hkΛ' : k ≤ Λ := by nlinarith only [hkΛ, hΛ, sq_nonneg (k - 1)]
  have hk4 : k ^ 4 ≤ z ^ 2 := by
    have hh := c.normSq_nonneg g (c.normalCurvatureDerivative g) x t
    rw [c.normSq_normalCurvatureDerivative g (Icc s u) hc.smooth hc.immersed x t ht, hk2, hz2] at hh
    nlinarith only [hh]
  have hP : |P| ≤ z * k := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt (g t) p _ _
  have hQ : |Q| ≤ w * k := DifferentialGeometry.Geometry.Riemannian.abs_inner_le_sqrt_mul_sqrt (g t) p _ _
  have hP2 : P ^ 2 ≤ k ^ 2 * z ^ 2 := by
    have hh := sq_le_sq₀ (abs_nonneg P) (mul_nonneg hz0 hk0) |>.mpr hP
    rw [sq_abs] at hh
    nlinarith only [hh]
  have hcross : -4 * k ^ 2 * Q ≤ w ^ 2 + 4 * k ^ 6 := by
    have hh := mul_le_mul_of_nonneg_left (abs_le.mp hQ).1 (by positivity : 0 ≤ 4 * k ^ 2)
    nlinarith only [hh, sq_nonneg (w - 2 * k ^ 3)]
  have hk6 : k ^ 6 ≤ Λ * z ^ 2 := by
    calc
      k ^ 6 = k ^ 2 * k ^ 4 := by ring
      _ ≤ Λ * z ^ 2 := mul_le_mul hkΛ hk4 (pow_nonneg hk0 4) hΛ0
  have hkz : k ^ 2 * z ^ 2 ≤ Λ * z ^ 2 := mul_le_mul_of_nonneg_right hkΛ (sq_nonneg z)
  have heuc : -2 * w ^ 2 - 4 * k ^ 2 * Q + 2 * k ^ 2 * z ^ 2 + 12 * P ^ 2 ≤
      -w ^ 2 + 18 * Λ * z ^ 2 := by
    linarith only [hP2, hcross, hk6, hkz]
  have hconn :
      G.rm04At t p (vec4 (Hc x t) (T x t) (Hc x t) (V x t)) -
        nablaRicci G t p (T x t) (Hc x t) (V x t) -
        nablaRicci G t p (Hc x t) (T x t) (V x t) +
        nablaRicci G t p (V x t) (T x t) (Hc x t) ≤ C * k ^ 2 * z + 3 * C * k * z := by
    have h1 := hR (Hc x t) (T x t) (Hc x t) (V x t)
    have h2 := hN (T x t) (Hc x t) (V x t)
    have h3 := hN (Hc x t) (T x t) (V x t)
    have h4 := hN (V x t) (T x t) (Hc x t)
    simp only [hnT, mul_one] at h1 h2 h3 h4
    have h1u := (abs_le.mp h1).2
    have h2l := (abs_le.mp h2).1
    have h3l := (abs_le.mp h3).1
    have h4u := (abs_le.mp h4).2
    linarith only [h1u, h2l, h3l, h4u]
  have hρ0 := mul_le_mul_of_nonneg_right (abs_le.mp hρ).2 (sq_nonneg z)
  have hρ1 : c.ds g (c.ricciTangent G) x t * P ≤ (C + 2 * C * k) * (z * k) :=
    (le_abs_self _).trans ((abs_mul _ _).le.trans
      (mul_le_mul hdρ hP (abs_nonneg _) (by positivity)))
  have hρ2 := mul_le_mul_of_nonneg_left (abs_le.mp hddρ).1 (sq_nonneg k)
  have hSV := (abs_le.mp hDS).2
  have hRV : -(C * z ^ 2) ≤ G.ricciAt t p (vec2 (V x t) (V x t)) := by
    have hh := (abs_le.mp (hRic (V x t) (V x t))).1
    nlinarith only [hh]
  have hamb : -2 * k ^ 2 * c.ds g (c.ds g (c.ricciTangent G)) x t +
      6 * c.ds g (c.ricciTangent G) x t * P + 6 * c.ricciTangent G x t * z ^ 2 +
      2 * c.ds g (S V) x t - 2 * S W x t +
      2 * G.rm04At t p (vec4 (Hc x t) (T x t) (Hc x t) (V x t)) -
      2 * nablaRicci G t p (T x t) (Hc x t) (V x t) -
      2 * nablaRicci G t p (Hc x t) (T x t) (V x t) +
      2 * nablaRicci G t p (V x t) (T x t) (Hc x t) -
      2 * G.ricciAt t p (vec2 (V x t) (V x t)) ≤
      C * (26 * k * z + 22 * k ^ 2 * z + 10 * z ^ 2 + 6 * z + 2 * k ^ 2 + 10 * k ^ 3 + 4 * k ^ 4) := by
    linarith only [hρ0, hρ1, hρ2, hSV, hconn, hRV]
  have hΛsq : Λ ≤ Λ ^ 2 := by nlinarith only [hΛ]
  have hk2Λ : k ^ 2 ≤ Λ ^ 2 := hkΛ.trans hΛsq
  have hk3Λ : k ^ 3 ≤ Λ ^ 2 := by
    have hh := mul_le_mul hkΛ hkΛ' hk0 hΛ0
    nlinarith only [hh]
  have hk4Λ : k ^ 4 ≤ Λ ^ 2 := by
    have hh := pow_le_pow_left₀ (sq_nonneg k) hkΛ 2
    nlinarith only [hh]
  have hzΛ : z ^ 2 ≤ Λ * z ^ 2 := by nlinarith only [mul_nonneg (sub_nonneg.mpr hΛ) (sq_nonneg z)]
  have hpoly : 26 * k * z + 22 * k ^ 2 * z + 10 * z ^ 2 + 6 * z + 2 * k ^ 2 + 10 * k ^ 3 + 4 * k ^ 4 ≤
      37 * Λ * z ^ 2 + 43 * Λ ^ 2 := by
    nlinarith only [sq_nonneg (k - z), sq_nonneg (k ^ 2 - z), sq_nonneg (z - 1), hk2Λ, hk3Λ, hk4Λ, hzΛ, hΛ.trans hΛsq]
  have hpolyC := mul_le_mul_of_nonneg_left hpoly hC0
  have hc1 : 18 + 37 * C ≤ 64 * (1 + C) := by linarith only [hC0]
  have hc2 : 43 * C ≤ 64 * (1 + C) := by linarith only [hC0]
  have hc1' := mul_le_mul_of_nonneg_right hc1 (mul_nonneg hΛ0 (sq_nonneg z))
  have hc2' := mul_le_mul_of_nonneg_right hc2 (sq_nonneg Λ)
  change derivWithin (c.normSq g V x) (Icc s u) t - c.ds g (c.ds g (c.normSq g V)) x t ≤ _
  rw [c.curvatureDerivative_evolution B hsu hwindow hc x t ht,
    c.ds_q G hc.smooth hc.immersed x t ht, c.ds_ds_q G hc.smooth hc.immersed x t ht]
  change -2 * c.normSq g W x t - 2 * c.curvatureSq g x t *
      (2 * Q + 2 * c.normSq g V x t + c.ds g (c.ds g (c.ricciTangent G)) x t) +
      6 * (2 * P + c.ds g (c.ricciTangent G) x t) * P +
      6 * (c.curvatureSq g x t + c.ricciTangent G x t) * c.normSq g V x t +
      2 * c.ds g (S V) x t - 2 * S W x t +
      2 * G.rm04At t p (vec4 (Hc x t) (T x t) (Hc x t) (V x t)) -
      2 * nablaRicci G t p (T x t) (Hc x t) (V x t) -
      2 * nablaRicci G t p (Hc x t) (T x t) (V x t) +
      2 * nablaRicci G t p (V x t) (T x t) (Hc x t) -
      2 * G.ricciAt t p (vec2 (V x t) (V x t)) ≤
      -c.normSq g W x t + 64 * (1 + C) * Λ * c.normSq g V x t + 64 * (1 + C) * Λ ^ 2
  rw [hk2, hz2, hw2]
  linarith only [heuc, hamb, hpolyC, hc1', hc2']

end CurveMap
end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
