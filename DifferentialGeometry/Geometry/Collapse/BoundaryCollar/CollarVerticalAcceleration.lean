import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspHeightHessian
import DifferentialGeometry.Geometry.Collapse.BoundaryScale.CuspAngleComparison
import DifferentialGeometry.Geometry.Collapse.BoundaryCollar.CollarHeightLevels

/-!
# Cusp verticals are almost geodesic (row BCP03, route R-V, step A1)

For a cusp embedding `e : CuspEmbedding W g K δ X` (`K ≥ 1`, `0 ≤ δ ≤ 1/4`) let `V` be the
vertical chart-constant field `∂_z` near a point `q` of the cusp domain, and
`w = ∇^g_{De ∂_z} (e_* ∂_z)` (Levi-Civita connection of `g`, `e_*` the pushforward through
`e⁻¹`).

* `cusp_leviCivita_vertical_vertical`: for the model metric, `∇^H_{∂_z} ∂_z = 0` (vertical lines
  of the cusp are geodesics): the three Koszul terms are derivatives of locally constant
  functions.
* `CuspEmbedding.vertical_acceleration_le`: `|w|_g ≤ 3δ` (the argument of FT-C's Z-H for
  `a = b = ∂_z`: the Koszul formula of `g` on pushforwards of chart-constant fields, compared with
  the Koszul formula of `H` and the Leibniz evaluation of `∇_H (e^*g − H)`).
* `CuspEmbedding.abs_iteratedDeriv_two_vertical_sub_hessian_le` (A1): for every smooth `f` on
  `W` and every vertical `s ↦ e(t, s)` at a height `0 < s < 100`,
  `|(f ∘ e(t, ·))''(s) − Hess_g f(De ∂_z, De ∂_z)| ≤ 3δ L` whenever `|df(u)| ≤ L |u|_g`.
-/

set_option autoImplicit false

noncomputable section

open Bundle Set Filter Function DifferentialGeometry DifferentialGeometry.Geometry.Hyperbolic
open DifferentialGeometry.Geometry.Connection DifferentialGeometry.Tensor0SBundle
open GC.Endpoint DifferentialGeometry.Topology.Manifold
open scoped Manifold ContDiff Topology

namespace DifferentialGeometry.Geometry.Collapse

universe u

local notation "Ec" => (EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)) × EuclideanSpace ℝ (Fin 1)
local notation "Et" => EuclideanSpace ℝ (Fin 1) × EuclideanSpace ℝ (Fin 1)

/-- The half-line is Hausdorff. -/
private theorem vertT2Half_BCP23 : T2Space (EuclideanHalfSpace 1) := by
  unfold EuclideanHalfSpace
  infer_instance

attribute [local instance] vertT2Half_BCP23

/-- The unit vertical vector of the cusp model space. -/
def cuspUnitVertical : Ec := ((0 : Et), EuclideanSpace.single 0 1)

/-- The Koszul formula for three differentiable vector fields with vanishing brackets at `x`. -/
private theorem vert_koszul {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [TopologicalSpace H] {I : ModelWithCorners ℝ E H}
    [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
    (G : SmoothRiemannianMetric I M) {X Y Z : (x : M) → TangentSpace I x} {x : M}
    (hX : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, X y⟩ : TotalSpace E (TangentSpace I))) x)
    (hY : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Y y⟩ : TotalSpace E (TangentSpace I))) x)
    (hZ : MDifferentiableAt I (I.prod 𝓘(ℝ, E)) (fun y => (⟨y, Z y⟩ : TotalSpace E (TangentSpace I))) x)
    (hXY : VectorField.mlieBracket I X Y x = 0) (hYZ : VectorField.mlieBracket I Y Z x = 0)
    (hZX : VectorField.mlieBracket I Z X x = 0) :
    G.inner x ((leviCivitaConnectionOfMetric G Y x) (X x)) (Z x) =
      (1 / 2 : ℝ) * (mvfderiv I (fun y => G.inner y (Y y) (Z y)) x (X x) +
        mvfderiv I (fun y => G.inner y (Z y) (X y)) x (Y x) -
        mvfderiv I (fun y => G.inner y (X y) (Y y)) x (Z x)) := by
  let : CompleteSpace E := FiniteDimensional.complete ℝ E
  have h := leviCivitaConnectionOfMetric_inner_eq_koszulScalar G X Y Z x hX hY hZ
  rw [h]
  simp only [koszulScalar, directionalDerivAlong, hXY, hYZ, hZX, map_zero, sub_zero, add_zero]

/-- The chart-constant fields at `q`, near `q`: the vertical one is literally `∂_z`. -/
private theorem vert_V_vertical (q : CuspHalfSpace)
    (V : Ec → ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hV : ∀ᶠ r in 𝓝 q, ∀ c : Ec, V c r = FiberBundle.extend
      (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec (x := q) c r) :
    ∀ᶠ r in 𝓝 q, ∀ c : Ec, (V c r).2 = c.2 ∧
      (V cuspUnitVertical r : TangentSpace halfCollarModel r) = cuspUnitVertical := by
  filter_upwards [(cusp_extend_eq_prod q).and hV] with r hr c
  refine ⟨by rw [hr.2 c, hr.1 c], ?_⟩
  rw [hr.2 cuspUnitVertical, hr.1 cuspUnitVertical]
  change (((trivializationAt Et (TangentSpace torusModel) q.1).symmL ℝ r.1 (0 : Et),
    EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) : Ec) = _
  rw [map_zero]
  rfl

/-- `H(∂_z, c) = c_z` for the model metric. -/
private theorem vert_model_inner_vertical (Hc : HyperbolicCusp) (r : CuspHalfSpace)
    (c : TangentSpace halfCollarModel r) :
    Hc.metric.inner r (cuspUnitVertical : TangentSpace halfCollarModel r) c = c.2 0 := by
  rw [Hc.metric_formula r cuspUnitVertical c]
  change (EuclideanSpace.single (0 : Fin 1) (1 : ℝ)) 0 * c.2 0 +
    Real.exp (-r.2.val 0) * Hc.torusMetric.inner r.1 (0 : Et) c.1 = c.2 0
  have h0 : Hc.torusMetric.inner r.1 (0 : Et) c.1 = 0 := by
    have := (Hc.torusMetric.inner r.1).map_zero
    exact congrArg (fun L : TangentSpace torusModel r.1 →L[ℝ] ℝ => L c.1) this
  rw [h0, mul_zero, add_zero]
  simp

/-- **Vertical lines of the cusp are geodesics**: `∇^H_{∂_z} ∂_z = 0` for chart-constant fields
at `q`. -/
theorem cusp_leviCivita_vertical_vertical (Hc : HyperbolicCusp) (q : CuspHalfSpace)
    (V : Ec → ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hV : ∀ᶠ r in 𝓝 q, ∀ c : Ec, V c r = FiberBundle.extend
      (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec (x := q) c r) :
    leviCivitaConnectionOfMetric Hc.metric (fun r => V cuspUnitVertical r) q cuspUnitVertical =
      0 := by
  have hVp : ∀ c : Ec, V c q = c := fun c => by
    rw [hV.self_of_nhds c]
    exact FiberBundle.extend_apply_self (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
      Ec (x := q) c
  have hV' : ∀ c : Ec, (fun r => (V c r : TangentSpace halfCollarModel r)) =ᶠ[𝓝 q]
      FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := q) c := fun c => hV.mono fun r hr => hr c
  have hbr : ∀ c c' : Ec, VectorField.mlieBracket halfCollarModel (fun r => V c r)
      (fun r => V c' r) q = 0 := fun c c' => by
    rw [(hV' c).mlieBracket_vectorField_eq (hV' c')]
    exact DifferentialGeometry.VectorField.mlieBracket_fiberBundleExtend_eq_zero q c c'
  have hd : ∀ c : Ec, MDifferentiableAt halfCollarModel (halfCollarModel.prod 𝓘(ℝ, Ec))
      (fun r => (⟨r, V c r⟩ : TotalSpace Ec (TangentSpace halfCollarModel))) q := fun c =>
    (V c).contMDiff.mdifferentiableAt (by simp)
  have hloc := vert_V_vertical q V hV
  -- the three inner products are locally constant
  have hconst1 : ∀ c : Ec, (fun r => Hc.metric.inner r (V cuspUnitVertical r) (V c r)) =ᶠ[𝓝 q]
      fun _ => c.2 0 := fun c => by
    filter_upwards [hloc] with r hr
    rw [(hr c).2, vert_model_inner_vertical, (hr c).1]
  have hconst2 : ∀ c : Ec, (fun r => Hc.metric.inner r (V c r) (V cuspUnitVertical r)) =ᶠ[𝓝 q]
      fun _ => c.2 0 := fun c => by
    filter_upwards [hconst1 c] with r hr
    rw [Hc.metric.symm]
    exact hr
  have hz : ∀ (φ : CuspHalfSpace → ℝ) (a : ℝ), φ =ᶠ[𝓝 q] (fun _ => a) →
      ∀ v : TangentSpace halfCollarModel q, mvfderiv halfCollarModel φ q v = 0 := by
    intro φ a hφ v
    rw [mvfderiv_eq_of_eventuallyEq hφ, mvfderiv_const]
    rfl
  set Γ : Ec := leviCivitaConnectionOfMetric Hc.metric (fun r => V cuspUnitVertical r) q
    cuspUnitVertical with hΓ
  by_contra hne
  have hpos := Hc.metric.pos q Γ hne
  have hk := vert_koszul Hc.metric (hd cuspUnitVertical) (hd cuspUnitVertical) (hd Γ)
    (hbr _ _) (hbr _ _) (hbr _ _)
  have e1 : mvfderiv halfCollarModel (fun y => Hc.metric.inner y (V cuspUnitVertical y) (V Γ y)) q
      (V cuspUnitVertical q) = 0 := hz _ _ (hconst1 Γ) _
  have e2 : mvfderiv halfCollarModel (fun y => Hc.metric.inner y (V Γ y) (V cuspUnitVertical y)) q
      (V cuspUnitVertical q) = 0 := hz _ _ (hconst2 Γ) _
  have e3 : mvfderiv halfCollarModel
      (fun y => Hc.metric.inner y (V cuspUnitVertical y) (V cuspUnitVertical y)) q (V Γ q) = 0 :=
    hz _ _ (hconst1 cuspUnitVertical) _
  rw [e1, e2, e3] at hk
  have hk' : Hc.metric.inner q Γ Γ = 0 := by
    have h1 : (V cuspUnitVertical q : TangentSpace halfCollarModel q) = cuspUnitVertical :=
      hVp cuspUnitVertical
    have h2 : (V Γ q : TangentSpace halfCollarModel q) = Γ := hVp Γ
    rw [h1, h2] at hk
    rw [hk]
    ring
  rw [hk'] at hpos
  exact lt_irrefl 0 hpos

private theorem vert_alg {δ na nb nD : ℝ} (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) (hna : 0 ≤ na)
    (hnb : 0 ≤ nb) (hnD : 0 ≤ nD)
    (hquad : (1 - δ) * nD ^ 2 ≤ (3 / 2 : ℝ) * (δ * na * nb * nD)) : nD ≤ 2 * δ * na * nb := by
  have hP : 0 ≤ δ * na * nb := by positivity
  by_contra hcon
  have hcon' : 2 * δ * na * nb < nD := lt_of_not_ge hcon
  have h1 : 2 * δ * na * nb * nD ≤ nD * nD := mul_le_mul_of_nonneg_right hcon'.le hnD
  nlinarith

variable {W : CompactCarrier.{u}} {g : SmoothRiemannianMetric W.model W.Carrier} {K : ℕ}
  {δ : ℝ} {X : Set W.Carrier}

/-- **Connection difference on pushforwards of chart-constant fields.** For chart-constant
fields `V` at `q` and `γ` with `De γ = ∇^g_{De a} (e_* V_b)`, the difference with the model
connection `∇^H_a V_b` has `H`-norm at most `2δ |a|_H |b|_H` (`K ≥ 1`, `0 ≤ δ ≤ 1/4`). -/
theorem CuspEmbedding.connection_pushforward_sub_model_le (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) {q : CuspHalfSpace} (hq : q ∈ cuspDomain)
    (V : Ec → ContMDiffSection halfCollarModel Ec ∞
      (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
    (hV : ∀ᶠ r in 𝓝 q, ∀ c : Ec, V c r = FiberBundle.extend
      (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec (x := q) c r)
    (a b γ : Ec)
    (hγ : mfderiv halfCollarModel W.model e.toFun q γ = leviCivitaConnectionOfMetric g
      (VectorField.mpullback W.model halfCollarModel (invFunOn e.toFun cuspDomain)
        (fun r => V b r)) (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q a))
    (Γab : Ec) (hΓab : Γab = leviCivitaConnectionOfMetric e.cusp.metric (fun r => V b r) q a) :
    Real.sqrt (e.cusp.metric.inner q (γ - Γab) (γ - Γab)) ≤
      2 * δ * Real.sqrt (e.cusp.metric.inner q a a) * Real.sqrt (e.cusp.metric.inner q b b) := by
  subst hΓab
  have hVp : ∀ c : Ec, V c q = c := fun c => by
    rw [hV.self_of_nhds c]
    exact FiberBundle.extend_apply_self (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
      Ec (x := q) c
  have hV' : ∀ c : Ec, (fun r => (V c r : TangentSpace halfCollarModel r)) =ᶠ[𝓝 q]
      FiberBundle.extend (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _)) Ec
        (x := q) c := fun c => hV.mono fun r hr => hr c
  have hbr : ∀ c c' : Ec, VectorField.mlieBracket halfCollarModel (fun r => V c r)
      (fun r => V c' r) q = 0 := fun c c' => by
    rw [(hV' c).mlieBracket_vectorField_eq (hV' c')]
    exact DifferentialGeometry.VectorField.mlieBracket_fiberBundleExtend_eq_zero q c c'
  have hd : ∀ c : Ec, MDifferentiableAt halfCollarModel (halfCollarModel.prod 𝓘(ℝ, Ec))
      (fun r => (⟨r, V c r⟩ : TotalSpace Ec (TangentSpace halfCollarModel))) q := fun c =>
    (V c).contMDiff.mdifferentiableAt (by simp)
  -- notation
  let Gp : Ec → Ec → ℝ := fun u v => g.inner (e.toFun q)
    (mfderiv halfCollarModel W.model e.toFun q u) (mfderiv halfCollarModel W.model e.toFun q v)
  let Hp : Ec → Ec → ℝ := fun u v => e.cusp.metric.inner q u v
  let Γ : Ec → Ec → Ec := fun x y =>
    leviCivitaConnectionOfMetric e.cusp.metric (fun r => V y r) q x
  let dG : Ec → Ec → Ec → ℝ := fun x y z => mvfderiv halfCollarModel (fun r => g.inner (e.toFun r)
    (mfderiv halfCollarModel W.model e.toFun r (V y r))
    (mfderiv halfCollarModel W.model e.toFun r (V z r))) q x
  let dH : Ec → Ec → Ec → ℝ := fun x y z => mvfderiv halfCollarModel
    (fun r => e.cusp.metric.inner r (V y r) (V z r)) q x
  let nT : Ec → Ec → Ec → ℝ := fun x y z =>
    metricCovariantDerivative e.cusp.metric 2 (cuspMetricError g e.cusp e.toFun) q
      (Fin.cons x ![y, z])
  -- Koszul on W
  have hKW : ∀ c : Ec, Gp γ c = (1 / 2 : ℝ) * (dG a b c + dG b c a - dG c a b) := fun c => by
    have h := e.inner_leviCivita_pushforward (g := g) hK hq (V a) (V b) (V c) (hbr a b) (hbr b c)
      (hbr c a)
    rw [hVp a, hVp b, hVp c] at h
    change g.inner (e.toFun q) (mfderiv halfCollarModel W.model e.toFun q γ)
      (mfderiv halfCollarModel W.model e.toFun q c) = _
    rw [hγ]
    exact h
  -- Koszul on the model
  have hKH : ∀ c : Ec, Hp (Γ a b) c = (1 / 2 : ℝ) * (dH a b c + dH b c a - dH c a b) :=
    fun c => by
    have h := vert_koszul e.cusp.metric (hd a) (hd b) (hd c) (hbr a b) (hbr b c) (hbr c a)
    rw [hVp a, hVp b, hVp c] at h
    exact h
  -- Leibniz evaluation of `∇T`
  have hG1 : ∀ x y z : Ec, nT x y z = dG x y z - dH x y z -
      ((Gp (Γ x y) z - Hp (Γ x y) z) + (Gp y (Γ x z) - Hp y (Γ x z))) := by
    intro x y z
    have h := e.metricCovariantDerivative_metricError_apply (g := g) hK hq (V x) (V y) (V z)
    rw [hVp x, hVp y, hVp z] at h
    exact h
  -- symmetries
  have hΓs : ∀ x y : Ec, Γ x y = Γ y x := fun x y => cusp_leviCivita_symm e.cusp q V hV x y
  have hGs : ∀ u v : Ec, Gp u v = Gp v u := fun u v => g.symm _ _ _
  have hHs : ∀ u v : Ec, Hp u v = Hp v u := fun u v => e.cusp.metric.symm _ _ _
  have hdGs : ∀ x y z : Ec, dG x y z = dG x z y := fun x y z => by
    change mvfderiv halfCollarModel (fun r => g.inner (e.toFun r)
      (mfderiv halfCollarModel W.model e.toFun r (V y r))
      (mfderiv halfCollarModel W.model e.toFun r (V z r))) q x =
      mvfderiv halfCollarModel (fun r => g.inner (e.toFun r)
      (mfderiv halfCollarModel W.model e.toFun r (V z r))
      (mfderiv halfCollarModel W.model e.toFun r (V y r))) q x
    congr 2
    funext r
    exact g.symm _ _ _
  have hdHs : ∀ x y z : Ec, dH x y z = dH x z y := fun x y z => by
    change mvfderiv halfCollarModel (fun r => e.cusp.metric.inner r (V y r) (V z r)) q x =
      mvfderiv halfCollarModel (fun r => e.cusp.metric.inner r (V z r) (V y r)) q x
    congr 2
    funext r
    exact e.cusp.metric.symm _ _ _
  -- the key identity
  have hkey : ∀ c : Ec, Gp (γ - Γ a b) c =
      (1 / 2 : ℝ) * (nT a b c + nT b c a - nT c a b) := fun c => by
    have e1 : Gp (γ - Γ a b) c = Gp γ c - Gp (Γ a b) c := by
      let L : Ec →L[ℝ] EuclideanSpace ℝ (Fin 3) := mfderiv halfCollarModel W.model e.toFun q
      let Bg : EuclideanSpace ℝ (Fin 3) →L[ℝ] EuclideanSpace ℝ (Fin 3) →L[ℝ] ℝ :=
        g.inner (e.toFun q)
      change Bg (L (γ - Γ a b)) (L c) = Bg (L γ) (L c) - Bg (L (Γ a b)) (L c)
      rw [map_sub, map_sub, sub_apply]
    have h1 := hG1 a b c
    have h2 := hG1 b c a
    have h3 := hG1 c a b
    have h4 := hKW c
    have h5 := hKH c
    rw [hΓs b a] at h2
    rw [hΓs c a, hΓs c b] at h3
    rw [hGs b (Γ a c), hHs b (Γ a c)] at h1
    rw [hGs c (Γ a b), hHs c (Γ a b)] at h2
    rw [hGs a (Γ b c), hHs a (Γ b c)] at h3
    rw [hdGs b c a, hdHs b c a] at h2
    rw [hdGs c a b, hdHs c a b] at h3
    rw [hdGs b c a, hdGs c a b] at h4
    rw [hdHs b c a, hdHs c a b] at h5
    rw [e1]
    linarith
  -- the bound on `γ - Γ a b`
  set Dv : Ec := γ - Γ a b with hDvdef
  have hnT : ∀ x y z : Ec, |nT x y z| ≤ δ * Real.sqrt (Hp x x) * Real.sqrt (Hp y y) *
      Real.sqrt (Hp z z) := fun x y z =>
    e.abs_metricCovariantDerivative_metricError_le (g := g) hK hq x y z
  have hDD := hkey Dv
  have hlow : (1 - δ) * Hp Dv Dv ≤ Gp Dv Dv := e.one_sub_mul_le_pullback_inner hq Dv
  set na := Real.sqrt (Hp a a) with hna
  set nb := Real.sqrt (Hp b b) with hnb
  set nD := Real.sqrt (Hp Dv Dv) with hnD
  have hna0 : 0 ≤ na := Real.sqrt_nonneg _
  have hnb0 : 0 ≤ nb := Real.sqrt_nonneg _
  have hnD0 : 0 ≤ nD := Real.sqrt_nonneg _
  have hDsq : Hp Dv Dv = nD ^ 2 := (Real.sq_sqrt (metric_inner_self_nonneg _ _ _)).symm
  have b1 := abs_le.mp (hnT a b Dv)
  have b2 := abs_le.mp (hnT b Dv a)
  have b3 := abs_le.mp (hnT Dv a b)
  have hup : Gp Dv Dv ≤ (3 / 2 : ℝ) * (δ * na * nb * nD) := by
    rw [hDD]
    linarith [b1.2, b2.2, b3.1]
  have hquad : (1 - δ) * nD ^ 2 ≤ (3 / 2 : ℝ) * (δ * na * nb * nD) := by
    rw [← hDsq]
    exact hlow.trans hup
  exact vert_alg hδ0 hδ hna0 hnb0 hnD0 hquad

attribute [-instance] Tensor0SBundle.tangentSpaceNormedAddCommGroup
  Tensor0SBundle.tangentSpaceNormedSpace in
/-- **A1: cusp verticals are almost geodesic.** For every smooth `f` on `W` with
`|df(u)| ≤ L |u|_g` at `e(t, s)`, `0 < s < 100`, the second derivative of `f` along the vertical
`σ ↦ e(t, σ)` differs from `Hess_g f(De ∂_z, De ∂_z)` by at most `3δ L` (`K ≥ 1`,
`0 ≤ δ ≤ 1/4`). -/
theorem CuspEmbedding.abs_iteratedDeriv_two_vertical_sub_hessian_le (e : CuspEmbedding W g K δ X)
    (hK : 1 ≤ K) (hδ0 : 0 ≤ δ) (hδ : δ ≤ 1 / 4) {f : W.Carrier → ℝ}
    (hf : ContMDiff W.model 𝓘(ℝ, ℝ) ∞ f) (t : Torus) {s : ℝ} (hs : 0 < s) (hs' : s < cuspDepth)
    {L : ℝ} (hL0 : 0 ≤ L)
    (hdf : ∀ u : TangentSpace W.model (e.toFun (t, halfSpaceOneLift s)),
      |mvfderiv W.model f (e.toFun (t, halfSpaceOneLift s)) u| ≤
        L * Real.sqrt (g.inner (e.toFun (t, halfSpaceOneLift s)) u u)) :
    |iteratedDeriv 2 (fun σ => f (e.toFun (t, halfSpaceOneLift σ))) s -
        (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian (LeviCivita g) f
          (e.toFun (t, halfSpaceOneLift s))
          (mfderiv halfCollarModel W.model e.toFun (t, halfSpaceOneLift s) cuspUnitVertical)
          (mfderiv halfCollarModel W.model e.toFun (t, halfSpaceOneLift s) cuspUnitVertical)| ≤
      3 * δ * L := by
  set q : CuspHalfSpace := (t, halfSpaceOneLift s) with hqdef
  have hqz : q.2.val 0 = s := by
    change (halfSpaceOneLift s).1 0 = s
    rw [halfSpaceOneLift_val_zero, max_eq_left hs.le]
  have hq : q ∈ cuspDomain := by
    change q.2.val 0 < cuspDepth
    rw [hqz]
    exact hs'
  obtain ⟨V, hV⟩ := cusp_exists_chartConstant_sections q
  have hVp : ∀ c : Ec, V c q = c := fun c => by
    rw [hV.self_of_nhds c]
    exact FiberBundle.extend_apply_self (E := (TangentSpace halfCollarModel : CuspHalfSpace → Type _))
      Ec (x := q) c
  set P := VectorField.mpullback W.model halfCollarModel (invFunOn e.toFun cuspDomain)
    (fun r => V cuspUnitVertical r) with hPdef
  set v : TangentSpace W.model (e.toFun q) :=
    mfderiv halfCollarModel W.model e.toFun q cuspUnitVertical with hvdef
  set w : TangentSpace W.model (e.toFun q) := leviCivitaConnectionOfMetric g P (e.toFun q) v
    with hwdef
  -- the bound `|w|_g ≤ 3δ`
  obtain ⟨A₀, hA⟩ := e.isInvertible_mfderiv hq
  let A : Ec ≃L[ℝ] EuclideanSpace ℝ (Fin 3) := A₀
  have hAD : ∀ c : Ec, A c = mfderiv halfCollarModel W.model e.toFun q c := fun c =>
    congrArg (fun T : TangentSpace halfCollarModel q →L[ℝ] TangentSpace W.model (e.toFun q) => T c)
      hA
  let γ : Ec := A.symm w
  have hγ : mfderiv halfCollarModel W.model e.toFun q γ = w := by
    rw [← hAD]
    exact A.apply_symm_apply w
  have hΓ0 := cusp_leviCivita_vertical_vertical e.cusp q V hV
  have hbound := e.connection_pushforward_sub_model_le hK hδ0 hδ hq V hV cuspUnitVertical
    cuspUnitVertical γ hγ 0 hΓ0.symm
  have hH1 : e.cusp.metric.inner q cuspUnitVertical cuspUnitVertical = 1 :=
    (vert_model_inner_vertical e.cusp q cuspUnitVertical).trans (by simp [cuspUnitVertical])
  rw [sub_zero, hH1, Real.sqrt_one, mul_one, mul_one] at hbound
  have hw : Real.sqrt (g.inner (e.toFun q) w w) ≤ 3 * δ := by
    have h1 := e.pullback_inner_le_one_add_mul hq γ
    rw [hγ] at h1
    have hHγ : 0 ≤ e.cusp.metric.inner q γ γ := metric_inner_self_nonneg _ _ _
    have h2 : Real.sqrt (g.inner (e.toFun q) w w) ≤
        Real.sqrt (1 + δ) * Real.sqrt (e.cusp.metric.inner q γ γ) := by
      rw [← Real.sqrt_mul (by linarith)]
      exact Real.sqrt_le_sqrt h1
    have h3 : Real.sqrt (1 + δ) ≤ 3 / 2 := by
      rw [show (3 / 2 : ℝ) = Real.sqrt ((3 / 2) ^ 2) from (Real.sqrt_sq (by norm_num)).symm]
      exact Real.sqrt_le_sqrt (by linarith)
    have h4 : 0 ≤ Real.sqrt (e.cusp.metric.inner q γ γ) := Real.sqrt_nonneg _
    calc Real.sqrt (g.inner (e.toFun q) w w)
        ≤ Real.sqrt (1 + δ) * Real.sqrt (e.cusp.metric.inner q γ γ) := h2
      _ ≤ 3 / 2 * (2 * δ) := mul_le_mul h3 hbound h4 (by norm_num)
      _ = 3 * δ := by ring
  -- the Hessian on the pushforward slot
  have hinvC2 := e.contMDiffAt_invFunOn_two hK hq
  have hP : MDifferentiableAt W.model (W.model.prod 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)))
      (fun y => (⟨y, P y⟩ : TotalSpace (EuclideanSpace ℝ (Fin 3)) (TangentSpace W.model)))
      (e.toFun q) :=
    MDifferentiableAt.mpullback_vectorField
      (((V cuspUnitVertical).contMDiff _).mdifferentiableAt (by simp)) hinvC2
      (e.isInvertible_mfderiv_invFunOn hq) le_rfl
  have hf2 : ContMDiffAt W.model 𝓘(ℝ, ℝ) 2 f (e.toFun q) := (hf _).of_le (by simp)
  have hσ : ContMDiffAt W.model (W.model.prod 𝓘(ℝ, ℝ)) 2 (fun y =>
      (⟨y, f y⟩ : TotalSpace ℝ (Bundle.Trivial W.Carrier ℝ))) (e.toFun q) :=
    (contMDiffAt_section (F := ℝ) (E := Bundle.Trivial W.Carrier ℝ) (e.toFun q)).mpr hf2
  have hcov : CovariantDerivative.ContMDiffCovariantDerivative
      (CovariantDerivative.trivial W.model W.Carrier ℝ) ∞ :=
    inferInstance
  have hD := (hcov.contMDiffAt (m := 1) hσ (by norm_num)).mdifferentiableAt (by simp)
  have h := (CovariantDerivative.trivial W.model W.Carrier ℝ).hessian_apply (LeviCivita g) hD hP v
  simp only [CovariantDerivative.trivial_apply] at h
  have hPq : P (e.toFun q) = v := by
    rw [hPdef, e.mpullback_invFunOn_apply hq (fun r => V cuspUnitVertical r), hVp]
  rw [hPq] at h
  -- the second derivative along the vertical
  set Ψ : W.Carrier → ℝ := fun y => mvfderiv W.model f y (P y) with hΨ
  have hΨd : MDifferentiableAt W.model 𝓘(ℝ, ℝ) Ψ (e.toFun q) :=
    mdifferentiableAt_pairing (mdiffAtCotangent_mvfderiv_of_contMDiffAt hf2) hP
  set c₀ : ℝ → CuspHalfSpace := fun σ => (t, halfSpaceOneLift σ) with hc₀
  set D0 : ℝ →L[ℝ] Ec := (0 : ℝ →L[ℝ] Et).prod
    (ContinuousLinearMap.toSpanSingleton ℝ (WithLp.toLp 2 (fun _ : Fin 1 => (1 : ℝ)))) with hD0
  have hc₀d : HasMFDerivAt 𝓘(ℝ, ℝ) halfCollarModel c₀ s D0 :=
    (hasMFDerivAt_const t s).prodMk (hasMFDerivAt_halfSpaceOneLift_of_pos hs)
  have hD01 : D0 1 = cuspUnitVertical := by
    rw [hD0]
    refine Prod.ext rfl ?_
    ext i
    fin_cases i
    simp [cuspUnitVertical]
  have hed : MDifferentiableAt halfCollarModel W.model e.toFun q :=
    (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hq)).mdifferentiableAt (by simp)
  have hcomp : HasMFDerivAt 𝓘(ℝ, ℝ) 𝓘(ℝ, ℝ) (fun σ => Ψ (e.toFun (c₀ σ))) s
      ((mfderiv W.model 𝓘(ℝ, ℝ) Ψ (e.toFun q)).comp
        ((mfderiv halfCollarModel W.model e.toFun q).comp D0)) :=
    hΨd.hasMFDerivAt.comp s (hed.hasMFDerivAt.comp s hc₀d)
  have hderivΨ : deriv (fun σ => Ψ (e.toFun (c₀ σ))) s = mvfderiv W.model Ψ (e.toFun q) v := by
    have h1 := hcomp.mfderiv
    rw [mfderiv_eq_fderiv] at h1
    have hv := congrArg (fun D => NormedSpace.fromTangentSpace (𝕜 := ℝ) (Ψ (e.toFun (c₀ s)))
      (D ((NormedSpace.fromTangentSpace (𝕜 := ℝ) s).symm (1 : ℝ)))) h1
    simp only [ContinuousLinearMap.comp_apply, ContinuousLinearEquiv.coe_coe,
      ContinuousLinearEquiv.apply_symm_apply, fderiv_apply_one_eq_deriv] at hv
    rw [hv]
    change (mfderiv W.model 𝓘(ℝ, ℝ) Ψ (e.toFun q))
      ((mfderiv halfCollarModel W.model e.toFun q) (D0 1)) = _
    rw [hD01]
    rfl
  -- `Ψ ∘ e ∘ c₀` is the first derivative of `f` along the vertical
  have hc₀cont : ContinuousAt c₀ s := hc₀d.continuousAt
  have hev : ∀ᶠ σ in 𝓝 s, 0 < σ ∧ σ < cuspDepth ∧ ∀ c : Ec, (V c (c₀ σ)).2 = c.2 ∧
      (V cuspUnitVertical (c₀ σ) : TangentSpace halfCollarModel (c₀ σ)) = cuspUnitVertical := by
    have h1 : ∀ᶠ σ in 𝓝 s, ∀ c : Ec, (V c (c₀ σ)).2 = c.2 ∧
        (V cuspUnitVertical (c₀ σ) : TangentSpace halfCollarModel (c₀ σ)) = cuspUnitVertical :=
      hc₀cont.eventually (vert_V_vertical q V hV)
    filter_upwards [Ioi_mem_nhds hs, Iio_mem_nhds hs', h1] with σ hσ1 hσ2 hσ3
    exact ⟨hσ1, hσ2, hσ3⟩
  have heq : (fun σ => Ψ (e.toFun (c₀ σ))) =ᶠ[𝓝 s]
      deriv (fun σ => f (e.toFun (t, halfSpaceOneLift σ))) := by
    filter_upwards [hev] with σ ⟨hσ0, hσ1, hσV⟩
    have hrz : (c₀ σ).2.val 0 = σ := by
      change (halfSpaceOneLift σ).1 0 = σ
      rw [halfSpaceOneLift_val_zero, max_eq_left hσ0.le]
    have hr : c₀ σ ∈ cuspDomain := by
      change (c₀ σ).2.val 0 < cuspDepth
      rw [hrz]
      exact hσ1
    have hvert := e.hasDerivAt_vertical (f := f) (x := t) hσ0 hσ1
      ((hf _).mdifferentiableAt (by simp))
    rw [hvert.deriv]
    change mvfderiv W.model f (e.toFun (c₀ σ)) (P (e.toFun (c₀ σ))) = _
    rw [hPdef, e.mpullback_invFunOn_apply hr (fun r => V cuspUnitVertical r), (hσV cuspUnitVertical).2]
    have hedr : MDifferentiableAt halfCollarModel W.model e.toFun (c₀ σ) :=
      (e.contMDiffOn.contMDiffAt (isOpen_cuspDomain.mem_nhds hr)).mdifferentiableAt (by simp)
    have hfr : MDifferentiableAt W.model 𝓘(ℝ, ℝ) f (e.toFun (c₀ σ)) :=
      (hf _).mdifferentiableAt (by simp)
    rw [mfderiv_comp (c₀ σ) hfr hedr]
    rfl
  have hiter : iteratedDeriv 2 (fun σ => f (e.toFun (t, halfSpaceOneLift σ))) s =
      mvfderiv W.model Ψ (e.toFun q) v := by
    rw [iteratedDeriv_succ, iteratedDeriv_one, ← heq.deriv_eq]
    exact hderivΨ
  rw [hiter, h, sub_sub_cancel]
  change |mvfderiv W.model f (e.toFun q) w| ≤ 3 * δ * L
  calc |mvfderiv W.model f (e.toFun q) w| ≤ L * Real.sqrt (g.inner (e.toFun q) w w) := hdf w
    _ ≤ L * (3 * δ) := mul_le_mul_of_nonneg_left hw hL0
    _ = 3 * δ * L := by ring

end DifferentialGeometry.Geometry.Collapse
