import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.Index.Trace
import DifferentialGeometry.Geometry.Flow.RicciFlow.Perelman.LGeometry.ReducedLength

set_option autoImplicit false

noncomputable section

namespace DifferentialGeometry.PDE.RicciFlow.Perelman

open Bundle Set
open scoped Manifold ContDiff Topology

open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Operator
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open MeasureTheory

universe u uE uH

variable {E : Type uE} [NormedAddCommGroup E] [InnerProductSpace Real E]
  [FiniteDimensional Real E]
  [NeZero (Module.finrank Real E)]
variable {H : Type uH} [TopologicalSpace H]
variable {I : ModelWithCorners Real E H} [I.Boundaryless]
variable {M : Type u} [PseudoMetricSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M] [T2Space M] [CompactSpace M]
variable {D : RealTimeInterval}

omit [FiniteDimensional Real E] [I.Boundaryless] [T2Space M]
  [CompactSpace M] in
private theorem exists_basis_eq_gON
    (g : SmoothRiemannianMetric I M) (x : M)
    (e : Fin (Module.finrank Real E) → TangentSpace I x)
    (hON : ∀ i j, g.inner x (e i) (e j) = if i = j then 1 else 0) :
    ∃ basis : Module.Basis (Fin (Module.finrank Real E)) Real (TangentSpace I x),
      ∀ i, basis i = e i := by
  classical
  let cd : InnerProductSpace.Core Real (TangentSpace I x) :=
    g.toRiemannianMetric.toCore x
  have hc : ContinuousAt (fun v : TangentSpace I x ↦ cd.inner v v) 0 :=
    g.toRiemannianMetric.continuousAt x
  have hbnd : Bornology.IsVonNBounded Real
      {v : TangentSpace I x | RCLike.re (cd.inner v v) < 1} :=
    g.toRiemannianMetric.isVonNBounded x
  let nag : NormedAddCommGroup (TangentSpace I x) :=
    cd.toNormedAddCommGroupOfTopology hc hbnd
  let ips : InnerProductSpace Real (TangentSpace I x) :=
    InnerProductSpace.ofCoreOfTopology cd hc hbnd
  have : Nonempty (Fin (Module.finrank Real E)) :=
    ⟨⟨0, NeZero.pos _⟩⟩
  have hinner : ∀ u v : TangentSpace I x,
      (inner Real u v : Real) = g.inner x u v := fun _ _ ↦ rfl
  have hon : Orthonormal Real e := by
    rw [orthonormal_iff_ite]
    intro i j
    rw [hinner (e i) (e j)]
    exact hON i j
  have hcard : Fintype.card (Fin (Module.finrank Real E)) =
      Module.finrank Real (TangentSpace I x) := by
    rw [Fintype.card_fin]
    rfl
  let basis : Module.Basis (Fin (Module.finrank Real E)) Real
      (TangentSpace I x) :=
    basisOfOrthonormalOfCardEqFinrank hon hcard
  refine ⟨basis, fun i ↦ ?_⟩
  exact congrFun (coe_basisOfOrthonormalOfCardEqFinrank hon hcard) i

theorem redLength_lap_le
    (S : SolutionOn (I := I) (M := M) D)
    (hS : IsSolutionOn (I := I) S) (T : Real) (x : M)
    {Z : TangentSpace I x} {tau : Real}
    (htau : 0 < tau) (hZ : Z ∈ lInjDomain S T x tau)
    (P : Fin (Module.finrank Real E) →
      ∀ s, TangentSpace I (lRegCurve S T x Z s))
    {Ω : Set Real} (hΩ : IsOpen Ω)
    (hΩseg : Set.Icc (0 : Real) (Real.sqrt tau) ⊆ Ω)
    (hW : ∀ i, ContMDiffOn (modelWithCornersSelf Real Real) I.tangent
      (8 : Nat)
      (fun s : Real ↦ (TotalSpace.mk' E
        (E := (TangentSpace I : M → Type _))
        (lRegCurve S T x Z s) ((s / Real.sqrt tau) • P i s) :
          TangentBundle I M)) Ω)
    (hP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      DifferentiableAt Real
        (chartRepAt (I := I) (lRegCurve S T x Z) (P i) s) s)
    (hDP : ∀ i s, s ∈ Set.Icc (0 : Real) (Real.sqrt tau) →
      covDerivAlong (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z) (P i) s =
        (-2 * s) • ricciSharp (I := I) (S.base.metric (T - s ^ 2))
          (lRegCurve S T x Z s) (P i s))
    (hON : ∀ i j,
      (S.base.metric (T - tau)).inner (lExp S T x Z tau)
          (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) =
        if i = j then 1 else 0)
    (hIint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (s / Real.sqrt tau) ^ 2 *
        lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s)
      MeasureTheory.volume 0 (Real.sqrt tau))
    (hRint : ∀ i, IntervalIntegrable
      (fun s : Real ↦ (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
        S.ricciAt (T - s ^ 2) (lRegCurve S T x Z s)
          (vec2 (P i s) (P i s)))
      MeasureTheory.volume 0 (Real.sqrt tau)) :
    laplacian (I := I) (LeviCivita (I := I)
        (S.base.metric (T - tau))) (S.base.metric (T - tau))
        (fun y : M ↦ redLength S T x y tau) (lExp S T x Z tau) ≤
      (Module.finrank Real E : Real) / (2 * tau) +
        (1 / Real.sqrt tau) *
          ∫ s in (0 : Real)..Real.sqrt tau,
            ((s / Real.sqrt tau) ^ 2 *
                ∑ i : Fin (Module.finrank Real E),
                  lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s) -
              (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
                S.scalar (T - s ^ 2) (lRegCurve S T x Z s) := by
  classical
  let b : Real := Real.sqrt tau
  let alpha : Real → M := lRegCurve S T x Z
  let y : M := lExp S T x Z tau
  let g : SmoothRiemannianMetric I M := S.base.metric (T - tau)
  rcases hZ with ⟨sigma, hsigma, hmin⟩
  have hZinj : Z ∈ lInjDomain S T x tau := ⟨sigma, hsigma, hmin⟩
  have hminTau : (Z, tau) ∈ lMinDomain S T x :=
    lMinDomain_down S hS T x Z hmin htau hsigma.le
  have hdom : (Z, tau) ∈ lExpPosDom S T x :=
    ((mem_lMinDomain S T x Z tau).1 hminTau).1
  have hb : 0 < b := by
    simpa only [b] using Real.sqrt_pos.2 htau
  have hbdom : b ∈ lRegDomain S T x Z := by
    simpa only [b] using
      ((mem_lExpPosDom S T x Z tau).1 hdom).2.2
  have hgeo := lRegCurve_isReg (I := I) S hS T x Z hb hbdom
  have ht : ∀ s ∈ Set.Icc (0 : Real) b, T - s ^ 2 ∈ D.regular := by
    intro s hs
    exact (hgeo.2.2 s (by
      simpa only [Set.uIcc_of_le hb.le] using hs)).1
  have halpha : ∀ s ∈ Set.Icc (0 : Real) b,
      MDifferentiableAt (modelWithCornersSelf Real Real) I alpha s := by
    intro s hs
    exact (hgeo.2.2 s (by
      simpa only [Set.uIcc_of_le hb.le] using hs)).2.1
  have hb_sq : b ^ 2 = tau := by
    simpa only [b] using Real.sq_sqrt htau.le
  have hONb : ∀ i j,
      (S.base.metric (T - b ^ 2)).inner (alpha b) (P i b) (P j b) =
        if i = j then 1 else 0 := by
    intro i j
    rw [hb_sq]
    change (S.base.metric (T - tau)).inner (lExp S T x Z tau)
      (P i (Real.sqrt tau)) (P j (Real.sqrt tau)) = _
    exact hON i j
  have hgb : g = S.base.metric (T - b ^ 2) := by
    dsimp only [g]
    rw [hb_sq]
  have hyb : y = alpha b := by
    rfl
  obtain ⟨basis, hbasis⟩ :=
    exists_basis_eq_gON (I := I) g y (fun i ↦ P i b) (by
      intro i j
      rw [hgb, hyb]
      exact hONb i j)
  have hONbasis : ∀ i j,
      g.inner y (basis i) (basis j) = if i = j then 1 else 0 := by
    intro i j
    rw [hbasis i, hbasis j]
    rw [hgb, hyb]
    exact hONb i j
  obtain ⟨U, hUopen, hyU, hsmooth⟩ :=
    redLength_smooth S hS T x htau hZinj
  have hlap :
      laplacian (I := I) (LeviCivita (I := I) g) g
          (fun q : M ↦ redLength S T x q tau) y =
        ∑ i : Fin (Module.finrank Real E),
          hessFun (I := I) g (fun q : M ↦ redLength S T x q tau) y
            (P i b) (P i b) := by
    have hlap0 := lap_eq_hess_on (I := I) g hUopen hsmooth hyU
    have htrace :
        metricTracePair0SAt (I := I) g
            (hessTensorAt (I := I) g
              (fun q : M ↦ redLength S T x q tau) y) =
          ∑ i : Fin (Module.finrank Real E),
            hessFun (I := I) g (fun q : M ↦ redLength S T x q tau) y
              (P i b) (P i b) := by
      rw [metricTracePair0SAt_eq_sum_basis (I := I) g basis
        (fun i j ↦ if i = j then (1 : Real) else 0)
        (metricInverseInBasis_of_orthonormal (I := I) g basis hONbasis)
        (hessTensorAt (I := I) g
          (fun q : M ↦ redLength S T x q tau) y)]
      simp only [hessTensorAt_apply]
      refine Finset.sum_congr rfl ?_
      intro i _
      rw [Finset.sum_eq_single i]
      · rw [if_pos rfl, one_mul, hbasis i]
      · intro j _ hji
        rw [if_neg (fun hij ↦ hji hij.symm), zero_mul]
      · intro hi
        exact absurd (Finset.mem_univ i) hi
    exact hlap0.trans htrace
  have hfield (i : Fin (Module.finrank Real E)) :
      hessFun (I := I) g (fun q : M ↦ redLength S T x q tau) y
          (P i b) (P i b) ≤
        lRegIndex S T alpha (fun s ↦ (s / b) • P i s)
            (fun s ↦ (s / b) • P i s) 0 b / b := by
    have hW0 : (fun s ↦ (s / b) • P i s) 0 = 0 := by
      simp only [zero_div, zero_smul]
    have hWb : (fun s ↦ (s / b) • P i s) b = P i b := by
      change (b / b) • P i b = P i b
      rw [div_self hb.ne', one_smul]
    simpa only [g, y, alpha, b] using
      redLength_hess_le S hS T x htau hZinj (P i b)
        (fun s ↦ (s / b) • P i s) hΩ
        (by simpa only [b] using hΩseg)
        (by simpa only [alpha, b] using hW i) hW0 hWb
  have htrace := lIndex_trace (I := I) S hS T alpha P b hb
    (by simpa only [alpha] using ht)
    (by simpa only [alpha] using halpha)
    (by simpa only [alpha, b] using hP)
    (by simpa only [alpha, b] using hDP) hONb
    (by simpa only [alpha, b] using hIint)
    (by simpa only [alpha, b] using hRint)
  rw [show S.base.metric (T - tau) = g from rfl,
    show lExp S T x Z tau = y from rfl, hlap]
  calc
    (∑ i : Fin (Module.finrank Real E),
        hessFun (I := I) g (fun q : M ↦ redLength S T x q tau) y
          (P i b) (P i b)) ≤
        ∑ i : Fin (Module.finrank Real E),
          lRegIndex S T alpha (fun s ↦ (s / b) • P i s)
            (fun s ↦ (s / b) • P i s) 0 b / b :=
      Finset.sum_le_sum fun i _ ↦ hfield i
    _ = (∑ i : Fin (Module.finrank Real E),
          lRegIndex S T alpha (fun s ↦ (s / b) • P i s)
            (fun s ↦ (s / b) • P i s) 0 b) / b := by
      rw [Finset.sum_div]
    _ = (Module.finrank Real E : Real) / (2 * tau) +
        (1 / Real.sqrt tau) *
          ∫ s in (0 : Real)..Real.sqrt tau,
            ((s / Real.sqrt tau) ^ 2 *
                ∑ i : Fin (Module.finrank Real E),
                  lRegIndexInt S T (lRegCurve S T x Z) (P i) (P i) s) -
              (2 * s ^ 2 / (Real.sqrt tau) ^ 2) *
                S.scalar (T - s ^ 2) (lRegCurve S T x Z s) := by
      rw [htrace]
      let A : Real :=
        ∫ s in (0 : Real)..b,
          ((s / b) ^ 2 *
              ∑ i : Fin (Module.finrank Real E),
                lRegIndexInt S T alpha (P i) (P i) s) -
            (2 * s ^ 2 / b ^ 2) * S.scalar (T - s ^ 2) (alpha s)
      change ((Module.finrank Real E : Real) / (2 * b) + A) / b =
        (Module.finrank Real E : Real) / (2 * tau) + (1 / b) * A
      rw [← hb_sq]
      field_simp [hb.ne']

end DifferentialGeometry.PDE.RicciFlow.Perelman
