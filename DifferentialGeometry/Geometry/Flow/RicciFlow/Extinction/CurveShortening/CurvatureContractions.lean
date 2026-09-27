import DifferentialGeometry.Geometry.Flow.RicciFlow.Extinction.CurveShortening.HigherDerivativeEvolution

noncomputable section
open Bundle Manifold Set
open scoped Manifold ContDiff Topology BigOperators
open DifferentialGeometry.Geometry.Curvature
open DifferentialGeometry.Geometry.Connection
open DifferentialGeometry.Geometry.Riemannian.CovariantDerivativeAlong
open DifferentialGeometry.Tensor0SBundle
open DifferentialGeometry.CheegerGromovCompactness

namespace DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening

inductive CurvatureTensorKind
  | ricci
  | riemann

abbrev CurvatureTensorKind.arity : CurvatureTensorKind → ℕ
  | .ricci => 2
  | .riemann => 4

inductive CurvatureContraction
  | inner (i j k : ℕ)
  | ricci (m : ℕ) (v : Fin (2 + m) → ℕ) (k : ℕ)
  | tensor (kind : CurvatureTensorKind) (m : ℕ)
      (p : Fin (kind.arity + m)) (v : Fin (kind.arity + m) → ℕ)

def CurvatureContraction.derivative : CurvatureContraction → List CurvatureContraction
  | .inner i j k => [.inner (i + 1) j k, .inner i (j + 1) k, .inner i j (k + 1)]
  | .ricci m v k =>
      .ricci (m + 1) (Fin.cons 0 v) k :: .ricci m v (k + 1) ::
        (Finset.univ.toList.map fun i => .ricci m (Function.update v i (v i + 1)) k)
  | .tensor kind m p v =>
      .tensor kind (m + 1) p.succ (Fin.cons 0 v) ::
        ((Finset.univ.erase p).toList.map fun i => .tensor kind m p (Function.update v i (v i + 1)))

def CurvatureContraction.Admissible (w n a : ℕ) : CurvatureContraction → Prop
  | .inner i j k => i + j + k ≤ w ∧ i ≤ n ∧ j ≤ n ∧ k ≤ n
  | .ricci m v k => (∑ i, v i) + k ≤ w ∧ (∀ i, v i ≤ n) ∧ k ≤ n ∧ m ≤ a
  | .tensor _ m p v => (∑ i ∈ Finset.univ.erase p, v i) ≤ w ∧
      (∀ i, i ≠ p → v i ≤ n) ∧ m ≤ a

private theorem sum_update_succ {ι : Type*} [DecidableEq ι] (S : Finset ι) (v : ι → ℕ)
    (i : ι) (hi : i ∈ S) : (∑ j ∈ S, Function.update v i (v i + 1) j) = (∑ j ∈ S, v j) + 1 := by
  rw [Finset.sum_update_of_mem hi, Finset.sdiff_singleton_eq_erase]
  have hh := Finset.sum_erase_add S v hi
  omega

private theorem sum_erase_cons_zero {r : ℕ} (p : Fin r) (v : Fin r → ℕ) :
    (∑ i ∈ Finset.univ.erase p.succ, Fin.cons 0 v i) = ∑ i ∈ Finset.univ.erase p, v i := by
  have h1 := Finset.sum_erase_add Finset.univ (Fin.cons (α := fun _ : Fin (r + 1) => ℕ) 0 v)
    (Finset.mem_univ p.succ)
  have h2 := Finset.sum_erase_add Finset.univ v (Finset.mem_univ p)
  simp only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_add] at h1
  omega

theorem CurvatureContraction.Admissible.derivative {w n a : ℕ} {A B : CurvatureContraction}
    (hA : A.Admissible w n a) (hB : B ∈ A.derivative) : B.Admissible (w + 1) (n + 1) (a + 1) := by
  cases A with
  | inner i j k =>
    simp only [CurvatureContraction.derivative, List.mem_cons, List.not_mem_nil, or_false] at hB
    rcases hB with rfl | rfl | rfl <;> dsimp [Admissible] at * <;> omega
  | ricci m v k =>
    rcases hA with ⟨hw, hn, hk, ha⟩
    simp only [CurvatureContraction.derivative, List.mem_cons, List.mem_map, Finset.mem_toList,
      Finset.mem_univ, true_and] at hB
    rcases hB with rfl | rfl | ⟨i, rfl⟩
    · refine ⟨?_, ?_, by omega, by omega⟩
      · change (∑ i : Fin (2 + m + 1), Fin.cons 0 v i) + k ≤ w + 1
        simpa only [Fin.sum_univ_succ, Fin.cons_zero, Fin.cons_succ, zero_add] using hw.trans (Nat.le_succ w)
      · intro j
        refine Fin.cases ?_ (fun j => ?_) j
        · exact Nat.zero_le _
        · exact (hn j).trans (Nat.le_succ n)
    · exact ⟨by omega, fun j => (hn j).trans (Nat.le_succ n), by omega, by omega⟩
    · refine ⟨?_, ?_, by omega, by omega⟩
      · rw [sum_update_succ Finset.univ v i (Finset.mem_univ i)]
        omega
      · intro j
        by_cases hj : j = i
        · subst j; simpa using Nat.add_le_add_right (hn i) 1
        · simpa only [Function.update_of_ne hj] using (hn j).trans (Nat.le_succ n)
  | tensor kind m p v =>
    rcases hA with ⟨hw, hn, ha⟩
    simp only [CurvatureContraction.derivative, List.mem_cons, List.mem_map, Finset.mem_toList] at hB
    rcases hB with rfl | ⟨i, hi, rfl⟩
    · refine ⟨?_, ?_, by omega⟩
      · erw [sum_erase_cons_zero]
        exact hw.trans (Nat.le_succ w)
      · intro j
        refine Fin.cases ?_ (fun l => ?_) j
        · intro _; exact Nat.zero_le _
        · intro hlp
          apply (hn l ?_).trans (Nat.le_succ n)
          exact fun hl => hlp (congrArg Fin.succ hl)
    · refine ⟨?_, ?_, by omega⟩
      · rw [sum_update_succ _ v i hi]
        omega
      · intro j hjp
        by_cases hj : j = i
        · subst j; simpa using Nat.add_le_add_right (hn i hjp) 1
        · simpa only [Function.update_of_ne hj] using (hn j hjp).trans (Nat.le_succ n)

def CurvatureContraction.derivativeExpansion (L : List (ℝ × CurvatureContraction)) :
    List (ℝ × CurvatureContraction) :=
  L.flatMap fun z => z.2.derivative.map fun A => (z.1, A)

def curvatureForcingIncrement (m : ℕ) : List (ℝ × CurvatureContraction) :=
  [(1, .inner 1 1 (m + 2)), (1, .ricci 0 ![0, 0] (m + 2)),
    (1, .tensor .riemann 0 3 ![1, 0, m + 1, 0]),
    (-1, .tensor .ricci 1 2 ![0, m + 1, 0]),
    (-1, .tensor .ricci 1 2 ![m + 1, 0, 0]),
    (1, .tensor .ricci 1 0 ![0, 0, m + 1])]

def curvatureForcingExpansion : ℕ → List (ℝ × CurvatureContraction)
  | 0 => [(2, .inner 2 1 0), (2, .inner 1 1 1),
      (1, .ricci 1 ![0, 0, 0] 0), (1, .ricci 0 ![1, 0] 0),
      (1, .ricci 0 ![0, 1] 0), (2, .ricci 0 ![0, 0] 1),
      (1, .tensor .riemann 0 3 ![1, 0, 0, 0]),
      (-2, .tensor .ricci 1 2 ![0, 0, 0]), (1, .tensor .ricci 1 0 ![0, 0, 0])]
  | m + 1 => CurvatureContraction.derivativeExpansion (curvatureForcingExpansion m) ++
      curvatureForcingIncrement m

private theorem sum_erase_le_of_sum_le {r : ℕ} (p : Fin r) (v : Fin r → ℕ) {w : ℕ}
    (h : (∑ i, v i) ≤ w) : (∑ i ∈ Finset.univ.erase p, v i) ≤ w :=
  (Finset.sum_le_sum_of_subset (Finset.erase_subset p Finset.univ)).trans h

private theorem curvature_forcing_increment_admissible (m : ℕ) (z : ℝ × CurvatureContraction)
    (hz : z ∈ curvatureForcingIncrement m) : z.2.Admissible (m + 4) (m + 3) (m + 2) := by
  simp only [curvatureForcingIncrement, List.mem_cons, List.not_mem_nil, or_false] at hz
  rcases hz with rfl | rfl | rfl | rfl | rfl | rfl
  · dsimp only [CurvatureContraction.Admissible]; omega
  · simp [CurvatureContraction.Admissible, Fin.sum_univ_two, Fin.forall_fin_succ]
  all_goals
    refine ⟨sum_erase_le_of_sum_le _ _ ?_, ?_, by omega⟩
    · simp [Fin.sum_univ_succ] <;> omega
    · simp [Fin.forall_fin_succ]

theorem curvature_forcing_expansion_admissible (m : ℕ) (z : ℝ × CurvatureContraction)
    (hz : z ∈ curvatureForcingExpansion m) : z.2.Admissible (m + 3) (m + 2) (m + 1) := by
  induction m generalizing z with
  | zero =>
    simp only [curvatureForcingExpansion, List.mem_cons, List.not_mem_nil, or_false] at hz
    rcases hz with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only [CurvatureContraction.Admissible] <;> decide
  | succ m ih =>
    simp only [curvatureForcingExpansion, List.mem_append] at hz
    rcases hz with hz | hz
    · simp only [CurvatureContraction.derivativeExpansion, List.mem_flatMap, List.mem_map] at hz
      obtain ⟨v, hv, A, hA, rfl⟩ := hz
      exact (ih v hv).derivative hA
    · exact curvature_forcing_increment_admissible m z hz

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
    {H : Type*} [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [I.Boundaryless]
    {M : Type*} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M] [T2Space M]

omit [I.Boundaryless] in
def CurvatureTensorKind.field (kind : CurvatureTensorKind) (G : SolutionFamily (I := I) (M := M))
    (m : ℕ) (t : ℝ) : Tensor0SField (I := I) (M := M) (n := ∞) (kind.arity + m) :=
  match kind with
  | .ricci => iterCov (G.metric t) 2 (G.ricci t) m
  | .riemann => iterCov (G.metric t) 4 (G.rm04 t) m

omit [I.Boundaryless] in
def CurvatureContraction.eval (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (A : CurvatureContraction) (x t : ℝ) : ℝ :=
  let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric) x t
  let ip := (G.metric t).inner (c.lift x t)
  match A with
  | .inner i j k => ip (Z i) (Z j) * ip (Z k) (W x t)
  | .ricci m v k =>
      CurvatureTensorKind.ricci.field G m t (c.lift x t) (fun i => Z (v i)) * ip (Z k) (W x t)
  | .tensor kind m p v =>
      kind.field G m t (c.lift x t) (Function.update (fun i => Z (v i)) p (W x t))

omit [I.Boundaryless] in
theorem CurvatureTensorKind.field_succ (kind : CurvatureTensorKind)
    (G : SolutionFamily (I := I) (M := M)) (m : ℕ) (t : ℝ) :
    kind.field G (m + 1) t = covStep (G.metric t) (kind.arity + m) (kind.field G m t) := by
  cases kind <;> rfl

theorem CurvatureContraction.differentiableAt_eval
    (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (W : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)))
    (A : CurvatureContraction) (x : ℝ) : DifferentiableAt ℝ (fun y => A.eval c G W y t) x := by
  classical
  let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric)
  have hZ (d : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Z d y t⟩ : TangentBundle I M)) :=
    c.iteratedDs_contMDiff G.metric hc hi _ t ht (c.unitTangent_contMDiff G.metric J hc hi t ht) d
  have hγ := contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  cases A with
  | inner i j k =>
    exact (c.differentiableAt_inner_slice G.metric J hc (Z i) (Z j) x t ht (hZ i) (hZ j)).mul
      (c.differentiableAt_inner_slice G.metric J hc (Z k) W x t ht (hZ k) hW)
  | ricci m v k =>
    exact ((c.contDiffAt_tensor_eval (CurvatureTensorKind.ricci.field G m t)
      (fun i => Z (v i)) x t (hγ x) (fun i => hZ (v i) x)).differentiableAt (by simp)).mul
      (c.differentiableAt_inner_slice G.metric J hc (Z k) W x t ht (hZ k) hW)
  | tensor kind m p v =>
    apply (c.contDiffAt_tensor_eval (kind.field G m t)
      (fun i y τ => Function.update (fun j => Z (v j) y τ) p (W y τ) i)
      x t (hγ x) ?_).differentiableAt (by simp)
    intro i
    by_cases hip : i = p
    · subst i; simpa using hW x
    · simpa only [Function.update_of_ne hip] using hZ (v i) x

theorem CurvatureContraction.ds_eval
    (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (W : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)))
    (A : CurvatureContraction) (x : ℝ) :
    c.ds G.metric (A.eval c G W) x t - A.eval c G (c.Ds G.metric W) x t =
      (A.derivative.map (fun A' => A'.eval c G W x t)).sum := by
  classical
  let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric)
  let ip := fun i j y τ => (G.metric τ).inner (c.lift y τ) (Z i y τ) (Z j y τ)
  let wp := fun i y τ => (G.metric τ).inner (c.lift y τ) (Z i y τ) (W y τ)
  have hZ (d : ℕ) : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
      (fun y => (⟨c.lift y t, Z d y t⟩ : TangentBundle I M)) :=
    c.iteratedDs_contMDiff G.metric hc hi _ t ht (c.unitTangent_contMDiff G.metric J hc hi t ht) d
  have hsucc (d : ℕ) : c.Ds G.metric (Z d) = Z (d + 1) := by
    simp only [Z, CurveMap.iteratedDs, Function.iterate_succ_apply']
  have hγ := contMDiffOn_univ.mp (c.space_slice_contMDiffOn J hc t ht)
  have hwp (i : ℕ) : c.ds G.metric (wp i) x t =
      wp (i + 1) x t + (G.metric t).inner (c.lift x t) (Z i x t) (c.Ds G.metric W x t) := by
    have hh := c.ds_inner G.metric J hc (Z i) W x t ht (hZ i) hW
    simpa only [hsucc] using hh
  have hdwp (i : ℕ) : DifferentiableAt ℝ (fun y => wp i y t) x :=
    c.differentiableAt_inner_slice G.metric J hc (Z i) W x t ht (hZ i) hW
  cases A with
  | inner i j k =>
    have hip : c.ds G.metric (ip i j) x t = ip (i + 1) j x t + ip i (j + 1) x t := by
      have hh := c.ds_inner G.metric J hc (Z i) (Z j) x t ht (hZ i) (hZ j)
      simpa only [hsucc] using hh
    have hprod := c.ds_mul G.metric (ip i j) (wp k) x t
      (c.differentiableAt_inner_slice G.metric J hc (Z i) (Z j) x t ht (hZ i) (hZ j)) (hdwp k)
    rw [hip, hwp] at hprod
    simp only [derivative, List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, eval]
    change c.ds G.metric (fun y τ => ip i j y τ * wp k y τ) x t - _ = _
    rw [hprod]
    dsimp only [ip, wp, Z]
    ring
  | ricci m v k =>
    let f := fun y τ => CurvatureTensorKind.ricci.field G m τ (c.lift y τ) (fun i => Z (v i) y τ)
    have hdf : DifferentiableAt ℝ (fun y => f y t) x :=
      (c.contDiffAt_tensor_eval (CurvatureTensorKind.ricci.field G m t)
        (fun i => Z (v i)) x t (hγ x) (fun i => hZ (v i) x)).differentiableAt (by simp)
    have hprod := c.ds_mul G.metric f (wp k) x t hdf (hdwp k)
    have hten := c.ds_tensor_eval (r := 2 + m) G.metric (fun τ => CurvatureTensorKind.ricci.field G m τ)
      (fun i => Z (v i)) x t ((hγ x).mdifferentiableAt (by simp))
      (fun i => chartRep_diff _ _ (hZ (v i)) x)
    simp_rw [hsucc] at hten
    rw [hwp] at hprod
    have hv (i : Fin (2 + m)) : (fun j => Z (Function.update v i (v i + 1) j) x t) =
        Function.update (fun j => Z (v j) x t) i (Z (v i + 1) x t) := by
      funext j
      by_cases hj : j = i
      · subst j; simp
      · simp only [Function.update_of_ne hj]
    have hhead : (fun i => Z (Fin.cons (α := fun _ : Fin (2 + m + 1) => ℕ) 0 v i) x t) = Fin.cons (c.unitTangent G.metric x t)
        (fun i => Z (v i) x t) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rfl
      · rfl
    simp_rw [← hv] at hten
    simp only [derivative, List.map_cons, List.map_map, Function.comp_def, List.sum_cons]
    dsimp only [eval]
    rw [CurvatureTensorKind.field_succ, covStep_apply]
    dsimp only [Z] at hhead
    erw [hhead]
    simp only [LeviCivita_eq_leviCivitaConnectionOfMetric] at hten
    change c.ds G.metric (fun y τ => f y τ * wp k y τ) x t - _ = _
    rw [hprod]
    change c.ds G.metric f x t = _ at hten
    rw [hten]
    simp only [Finset.sum_map_toList]
    rw [← Finset.sum_mul]
    dsimp only [wp, f, Z]
    ring
  | tensor kind m p v =>
    have hh := c.ds_tensor_eval_update G.metric (fun τ => kind.field G m τ)
      (fun i => Z (v i)) W p x t ((hγ x).mdifferentiableAt (by simp))
      (fun i => chartRep_diff _ _ (hZ (v i)) x) (chartRep_diff _ _ hW x)
    simp_rw [hsucc] at hh
    have hhead : Function.update (fun i => Z (Fin.cons (α := fun _ : Fin (kind.arity + m + 1) => ℕ) 0 v i) x t) p.succ (W x t) =
        Fin.cons (c.unitTangent G.metric x t) (Function.update (fun i => Z (v i) x t) p (W x t)) := by
      funext i
      refine Fin.cases ?_ (fun j => ?_) i
      · rw [Function.update_of_ne (Fin.succ_ne_zero p).symm, Fin.cons_zero]
        rfl
      · by_cases hj : j = p
        · subst j; simp
        · simp [hj]
    have hv (i : Fin (kind.arity + m)) (hi : i ∈ Finset.univ.erase p) :
        Function.update (fun j => Z (Function.update v i (v i + 1) j) x t) p (W x t) =
        Function.update (Function.update (fun j => Z (v j) x t) p (W x t)) i (Z (v i + 1) x t) := by
      have hip := Finset.ne_of_mem_erase hi
      funext j
      by_cases hjp : j = p
      · subst j; simp [Ne.symm hip]
      · by_cases hji : j = i
        · subst j; simp [hip]
        · simp only [Function.update_of_ne hjp, Function.update_of_ne hji]
    simp only [derivative, List.map_cons, List.map_map, Function.comp_def, List.sum_cons]
    dsimp only [eval]
    rw [CurvatureTensorKind.field_succ, covStep_apply]
    dsimp only [Z] at hhead
    erw [hhead]
    simp only [LeviCivita_eq_leviCivitaConnectionOfMetric] at hh
    rw [Finset.sum_map_toList]
    erw [hh]
    congr 1
    apply Finset.sum_congr rfl
    intro i hi
    dsimp only [Z] at hv
    erw [hv i hi]

omit [I.Boundaryless] in
def CurvatureContraction.evalExpansion (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (L : List (ℝ × CurvatureContraction)) (x t : ℝ) : ℝ :=
  (L.map fun z => z.1 * z.2.eval c G W x t).sum

theorem CurvatureContraction.differentiableAt_evalExpansion
    (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (W : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)))
    (L : List (ℝ × CurvatureContraction)) (x : ℝ) :
    DifferentiableAt ℝ (fun y => evalExpansion c G W L y t) x := by
  induction L with
  | nil => exact differentiableAt_const 0
  | cons z L ih =>
    exact ((z.2.differentiableAt_eval c G hc hi W t ht hW x).const_mul z.1).add ih

theorem CurvatureContraction.ds_evalExpansion
    (c : CurveMap M) (G : SolutionFamily (I := I) (M := M)) {J : Set ℝ}
    (hc : c.SmoothOn (I := I) J) (hi : c.ImmersedOn (I := I) J)
    (W : c.Field (I := I)) (t : ℝ) (ht : t ∈ J)
    (hW : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞ (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)))
    (L : List (ℝ × CurvatureContraction)) (x : ℝ) :
    c.ds G.metric (evalExpansion c G W L) x t - evalExpansion c G (c.Ds G.metric W) L x t =
      evalExpansion c G W (derivativeExpansion L) x t := by
  induction L with
  | nil => simp [evalExpansion, derivativeExpansion, CurveMap.ds]
  | cons z L ih =>
    have hds := c.ds_add G.metric (fun y τ => z.1 * z.2.eval c G W y τ)
      (evalExpansion c G W L) x t
      ((z.2.differentiableAt_eval c G hc hi W t ht hW x).const_mul z.1)
      (differentiableAt_evalExpansion c G hc hi W t ht hW L x)
    have hmul : c.ds G.metric (fun y τ => z.1 * z.2.eval c G W y τ) x t =
        z.1 * c.ds G.metric (z.2.eval c G W) x t := by
      rw [CurveMap.ds, CurveMap.ds, deriv_const_mul_field]
      ring
    rw [hmul] at hds
    have hz := z.2.ds_eval c G hc hi W t ht hW x
    simp only [evalExpansion, List.map_cons, List.sum_cons, derivativeExpansion,
      List.flatMap_cons, List.map_append, List.sum_append, List.map_map, Function.comp_def]
    change c.ds G.metric (fun y τ => z.1 * z.2.eval c G W y τ + evalExpansion c G W L y τ) x t - _ = _
    rw [hds, List.sum_map_mul_left]
    change _ = z.1 * (z.2.derivative.map (fun A => A.eval c G W x t)).sum +
      evalExpansion c G W (derivativeExpansion L) x t
    rw [← hz, ← ih]
    dsimp only [evalExpansion]
    ring

omit [I.Boundaryless] in
private theorem eval_ricci_zero (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (i j k : ℕ) (x t : ℝ) :
    CurvatureContraction.eval c G W (.ricci 0 ![i, j] k) x t =
      let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric) x t
      G.ricciAt t (c.lift x t) (vec2 (Z i) (Z j)) *
        (G.metric t).inner (c.lift x t) (Z k) (W x t) := by
  dsimp only [CurvatureContraction.eval, CurvatureTensorKind.field, iterCov]
  congr 1
  apply congrArg (G.ricciAt t (c.lift x t))
  funext l
  fin_cases l <;> rfl

omit [I.Boundaryless] in
private theorem eval_ricci_one (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (i j k l : ℕ) (x t : ℝ) :
    CurvatureContraction.eval c G W (.ricci 1 ![i, j, k] l) x t =
      let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric) x t
      nablaRicci G t (c.lift x t) (Z i) (Z j) (Z k) *
        (G.metric t).inner (c.lift x t) (Z l) (W x t) := by
  dsimp only [CurvatureContraction.eval, CurvatureTensorKind.field, iterCov]
  erw [covStep_apply]
  dsimp only [nablaRicci, SolutionFamily.connection]
  congr 1
  congr 1
  funext l
  fin_cases l <;> rfl

omit [I.Boundaryless] in
private theorem eval_riemann_last (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (i j k : ℕ) (x t : ℝ) :
    CurvatureContraction.eval c G W (.tensor .riemann 0 3 ![i, j, k, 0]) x t =
      let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric) x t
      G.rm04At t (c.lift x t) (vec4 (Z i) (Z j) (Z k) (W x t)) := by
  dsimp only [CurvatureContraction.eval, CurvatureTensorKind.field, iterCov]
  apply congrArg (G.rm04At t (c.lift x t))
  funext l
  fin_cases l <;> rfl

omit [I.Boundaryless] in
private theorem eval_nablaRicci_last (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (i j : ℕ) (x t : ℝ) :
    CurvatureContraction.eval c G W (.tensor .ricci 1 2 ![i, j, 0]) x t =
      let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric) x t
      nablaRicci G t (c.lift x t) (Z i) (Z j) (W x t) := by
  dsimp only [CurvatureContraction.eval, CurvatureTensorKind.field, iterCov]
  erw [covStep_apply]
  dsimp only [nablaRicci, SolutionFamily.connection]
  congr 1
  funext l
  fin_cases l <;> rfl

omit [I.Boundaryless] in
private theorem eval_nablaRicci_first (c : CurveMap M) (G : SolutionFamily (I := I) (M := M))
    (W : c.Field (I := I)) (i j : ℕ) (x t : ℝ) :
    CurvatureContraction.eval c G W (.tensor .ricci 1 0 ![0, i, j]) x t =
      let Z := fun d => c.iteratedDs G.metric d (c.unitTangent G.metric) x t
      nablaRicci G t (c.lift x t) (W x t) (Z i) (Z j) := by
  dsimp only [CurvatureContraction.eval, CurvatureTensorKind.field, iterCov]
  erw [covStep_apply]
  dsimp only [nablaRicci, SolutionFamily.connection]
  congr 1
  funext l
  fin_cases l <;> rfl

variable [CompleteSpace E] [SigmaCompactSpace M] {D : RealTimeInterval} {a b s u : ℝ}

private theorem curvature_forcing_zero_eval
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (W : c.Field (I := I)) (x t : ℝ) (ht : t ∈ Icc s u) :
    let g := B.family.metric
    (g t).inner (c.lift x t)
      (c.Dt g (Icc s u) (c.curvatureVector g) x t - c.iteratedDs g 2 (c.curvatureVector g) x t) (W x t) =
      CurvatureContraction.evalExpansion c B.family W (curvatureForcingExpansion 0) x t := by
  dsimp only
  rw [c.Dt_curvatureVector B hsu hwindow hc x t ht]
  simp only [map_sub, map_add, sub_apply, add_apply, map_smul, smul_apply, smul_eq_mul]
  rw [CurveMap.inner_riemannVector_eq_rm04 B.family, rfs_csf_connection B t (hwindow ht),
    c.ds_q B.family hc.smooth hc.immersed x t ht,
    c.ds_ricciTangent B.family hc.smooth hc.immersed x t ht]
  simp only [curvatureForcingExpansion, CurvatureContraction.evalExpansion, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, eval_ricci_zero, eval_ricci_one,
    eval_riemann_last, eval_nablaRicci_last, eval_nablaRicci_first]
  simp only [CurvatureContraction.eval, CurveMap.iteratedDs_unitTangent_succ]
  dsimp only [CurveMap.iteratedDs, CurveMap.q, CurveMap.ricciTangent, CurveMap.curvatureSq, CurveMap.normSq]
  simp only [Function.iterate_zero, Function.iterate_succ_apply', id_eq]
  ring

omit [SigmaCompactSpace M] [I.Boundaryless] in
private theorem curvature_forcing_increment_eval (c : CurveMap M)
    (G : SolutionFamily (I := I) (M := M)) (W : c.Field (I := I)) (m : ℕ) (x t : ℝ) :
    CurvatureContraction.evalExpansion c G W (curvatureForcingIncrement m) x t =
      let g := G.metric
      let V := fun j => c.iteratedDs g j (c.curvatureVector g)
      c.q G x t * (g t).inner (c.lift x t) (V (m + 1) x t) (W x t) +
      G.rm04At t (c.lift x t) (vec4 (c.curvatureVector g x t) (c.unitTangent g x t) (V m x t) (W x t)) -
      nablaRicci G t (c.lift x t) (c.unitTangent g x t) (V m x t) (W x t) -
      nablaRicci G t (c.lift x t) (V m x t) (c.unitTangent g x t) (W x t) +
      nablaRicci G t (c.lift x t) (W x t) (c.unitTangent g x t) (V m x t) := by
  simp only [curvatureForcingIncrement, CurvatureContraction.evalExpansion, List.map_cons,
    List.map_nil, List.sum_cons, List.sum_nil, eval_ricci_zero,
    eval_riemann_last, eval_nablaRicci_last, eval_nablaRicci_first]
  simp only [CurvatureContraction.eval, CurveMap.iteratedDs_unitTangent_succ]
  dsimp only [CurveMap.q, CurveMap.ricciTangent, CurveMap.curvatureSq, CurveMap.normSq]
  simp only [CurveMap.iteratedDs, Function.iterate_zero, id_eq]
  ring

theorem CurveMap.curvature_forcing_eq_expansion
    (B : RicciBackground (I := I) (M := M) D a b) (hsu : s < u) (hwindow : Icc s u ⊆ Icc a b)
    (c : CurveMap M) (hc : c.IsSolutionOn B.family.metric (Icc s u))
    (m : ℕ) (W : c.Field (I := I)) (hW : W.SmoothOn (I := I) (Icc s u))
    (x t : ℝ) (ht : t ∈ Icc s u) :
    let g := B.family.metric
    (g t).inner (c.lift x t)
      (c.Dt g (Icc s u) (c.iteratedDs g m (c.curvatureVector g)) x t -
        c.iteratedDs g (m + 2) (c.curvatureVector g) x t) (W x t) =
      CurvatureContraction.evalExpansion c B.family W (curvatureForcingExpansion m) x t := by
  induction m generalizing W x t with
  | zero => exact curvature_forcing_zero_eval B hsu hwindow c hc W x t ht
  | succ m ih =>
    let g := B.family.metric
    let V := fun j => c.iteratedDs g j (c.curvatureVector g)
    let R : ℕ → c.Field (I := I) := fun j y τ => c.Dt g (Icc s u) (V j) y τ - V (j + 2) y τ
    have hJ : Icc s u ⊆ D.regular := fun τ hτ => B.regular (hwindow hτ)
    have hDW := CurveMap.Field.smoothOn_Ds g B.smooth hJ (uniqueDiffOn_Icc hsu)
      c hc.smooth hc.immersed W hW
    have hWslice : ContMDiff 𝓘(ℝ, ℝ) I.tangent ∞
        (fun y => (⟨c.lift y t, W y t⟩ : TangentBundle I M)) :=
      fun y => contMDiffWithinAt_univ.mp (CurveShortening.Field.space_slice_contMDiffWithinAt c _ W hW y t ht)
    have heq : (fun y => (g t).inner (c.lift y t) (R m y t) (W y t)) =
        fun y => CurvatureContraction.evalExpansion c B.family W (curvatureForcingExpansion m) y t := by
      funext y
      exact ih W hW y t ht
    have hds : c.ds g (fun y τ => (g τ).inner (c.lift y τ) (R m y τ) (W y τ)) x t =
        c.ds g (CurvatureContraction.evalExpansion c B.family W (curvatureForcingExpansion m)) x t := by
      dsimp only [CurveMap.ds]
      rw [heq]
    have hforce := c.iteratedDs_curvature_forcing_pairing_succ B hsu hwindow hc W hW m x t ht
    change (g t).inner (c.lift x t) (R (m + 1) x t) (W x t) = _ at hforce
    rw [hds, ih (c.Ds g W) hDW x t ht] at hforce
    have hexp := CurvatureContraction.ds_evalExpansion c B.family hc.smooth hc.immersed W t ht
      hWslice (curvatureForcingExpansion m) x
    rw [hexp] at hforce
    simp only [curvatureForcingExpansion, CurvatureContraction.evalExpansion, List.map_append, List.sum_append]
    change (g t).inner (c.lift x t) (R (m + 1) x t) (W x t) =
      CurvatureContraction.evalExpansion c B.family W
        (CurvatureContraction.derivativeExpansion (curvatureForcingExpansion m)) x t +
      CurvatureContraction.evalExpansion c B.family W (curvatureForcingIncrement m) x t
    rw [curvature_forcing_increment_eval c B.family W m x t]
    exact hforce.trans (by ring)

end DifferentialGeometry.PDE.RicciFlow.Extinction.CurveShortening
