import DifferentialGeometry.Geometry.Flow.RicciFlow.LongTime.Ch11.AccuracyDecayC11RA

set_option autoImplicit false

/-!
# S-CH11-REPROVE-A (G2)：S2 = `RadiusAntitoneSupply_C11S q` 的参数级重证

astra 里 S2 = narrow tuple 的 `AntitoneOn q.neckRadius (Ici 0)`，来自
`SH/PreparedSpatialSurgery.lean:147` 的 `CutoffParameters.diagonal_neckRadius_antitone p …`
（W8 `ST/CutoffParameterGluing` **已有**，不需要重证）加每个 state 的 `radius_antitone` 字段。
W8 缺的只是「把它包成 SKEL 的 S2 谓词」与「链形 / tuple 的 `hpref` 形」的适配，这里补：

* `radiusAntitoneSupply_diagonal_C11RA` / `radiusAntitoneSupply_spliceAfter_C11RA`：W8 两个
  `neckRadius` antitone 引理的 S2 形；
* `radiusAntitoneSupply_congr_C11RA`：S2 只看 `t ≥ 0`，所以与 `ρ` 在 `[0,∞)` 一致的 `q` 同样成立；
* `chain_diagonal_radius_antitone_C11RA`：G1 的参数链（`parameters_past` + 每个 `L n` 的 ρ antitone）；
* **主定理** `radiusAntitone_of_chain_C11RA`：tuple 的 `hpref` 形 `q`（按 observation 与 diagonal 一致）
  满足 `RadiusAntitoneSupply_C11S q`；
* `chain_S1_S2_C11RA`：S1 + S2 一并给出（W1 里 q 的 antitone / 极限合取项）；
* consumer：G1 的 step 链上 S1 + S2 同时成立（`stepChain_S1_S2_C11RA`）。
-/

noncomputable section

open DifferentialGeometry.PDE.RicciFlow.Surgery.Topology Set Filter

namespace GC.LongTime.Ch11

/-! ## S2 形的 diagonal / splice -/

/-- prefix-compatible 且各自在 `[0,n]` 上 antitone 的 ρ 序列的对角满足 S2
（W8 `CutoffParameters.diagonal_neckRadius_antitone` 的 S2 形）。 -/
theorem radiusAntitoneSupply_diagonal_C11RA (p : ℕ → CutoffParameters)
    (hcompat : ∀ m n : ℕ, m ≤ n → ∀ t ∈ Icc (0 : ℝ) (m : ℝ),
      (p m).neckRadius t = (p n).neckRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (p n).neckRadius (Icc (0 : ℝ) (n : ℝ))) :
    RadiusAntitoneSupply_C11S (CutoffParameters.diagonal p) :=
  CutoffParameters.diagonal_neckRadius_antitone p hcompat hanti

/-- join 处满足 `q.neckRadius T ≤ p.neckRadius T` 的 splice 满足 S2
（W8 `CutoffParameters.spliceAfter_neckRadius_antitone` 的 S2 形）。 -/
theorem radiusAntitoneSupply_spliceAfter_C11RA (p q : CutoffParameters) (T : ℝ)
    (hp : AntitoneOn p.neckRadius (Icc 0 T)) (hq : AntitoneOn q.neckRadius (Ici T))
    (hjoin : q.neckRadius T ≤ p.neckRadius T) :
    RadiusAntitoneSupply_C11S (p.spliceAfter q T) :=
  CutoffParameters.spliceAfter_neckRadius_antitone p q T hp hq hjoin

/-- S2 只看 `t ≥ 0` 上的值：在 `[0,∞)` 上与 `q'` 一致的 `q` 同样满足 S2。 -/
theorem radiusAntitoneSupply_congr_C11RA {q q' : CutoffParameters}
    (heq : ∀ t : ℝ, 0 ≤ t → q.neckRadius t = q'.neckRadius t)
    (h : RadiusAntitoneSupply_C11S q') : RadiusAntitoneSupply_C11S q := by
  intro s hs t ht hst
  rw [heq t ht, heq s hs]
  exact h hs ht hst

/-! ## 参数链形 -/

/-- 链的 diagonal ρ antitone（reference：`SH/PreparedSpatialSurgery.lean:147`，输入每个 state 的
`radius_antitone`）。 -/
theorem chain_diagonal_radius_antitone_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hradius : ∀ n : ℕ, AntitoneOn (L n).neckRadius (Ici 0)) :
    RadiusAntitoneSupply_C11S (CutoffParameters.diagonal fun n => L (n + 1)) :=
  radiusAntitoneSupply_diagonal_C11RA _
    (fun m n hmn t ht =>
      (chain_diagonal_compat_C11RA E hElt hEge L hpast m n hmn t ht).2.1)
    (fun n _ hs _ ht hst => hradius (n + 1) hs.1 ht.1 hst)

/-- **G2 主定理（S2）**：tuple 的 `hpref` 形 `q`（`[0,n]` 上按 observation `n` 与链的 diagonal 一致）
满足 `RadiusAntitoneSupply_C11S q`。 -/
theorem radiusAntitone_of_chain_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hradius : ∀ n : ℕ, AntitoneOn (L n).neckRadius (Ici 0))
    (q : CutoffParameters)
    (hq : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.neckRadius t = (L (n + 1)).neckRadius t) :
    RadiusAntitoneSupply_C11S q :=
  radiusAntitoneSupply_congr_C11RA
    (q' := CutoffParameters.diagonal fun n => L (n + 1))
    (fun t ht => hq (Nat.ceil t) t ⟨ht, Nat.le_ceil t⟩)
    (chain_diagonal_radius_antitone_C11RA E hElt hEge L hpast hradius)

/-- **S1 + S2 一并**：W1 里 `q` 的 `AntitoneOn q.delta`、`AntitoneOn q.neckRadius`、
`Tendsto q.delta atTop (𝓝 0)` 三个合取项（外加 S1 的 decay 形）。 -/
theorem chain_S1_S2_C11RA (E : ℕ → ℝ) (hElt : ∀ n, E n < E (n + 1))
    (hEge : ∀ n : ℕ, (n : ℝ) ≤ E (n + 1)) (L : ℕ → CutoffParameters)
    (hpast : ∀ n : ℕ, ∀ t : ℝ, t ≤ E n →
      (L (n + 1)).delta t = (L n).delta t ∧
      (L (n + 1)).neckRadius t = (L n).neckRadius t ∧
      (L (n + 1)).protectedRadius t = (L n).protectedRadius t)
    (hanti : ∀ n : ℕ, AntitoneOn (L n).delta (Ici 0))
    (hradius : ∀ n : ℕ, AntitoneOn (L n).neckRadius (Ici 0))
    (a : ℕ → ℝ) (hafter : ∀ n : ℕ, ∀ t : ℝ, E n < t → (L (n + 1)).delta t = a n)
    (ha : ∀ n : ℕ, a n ≤ 1 / ((n : ℝ) + 2))
    (q : CutoffParameters)
    (hqδ : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.delta t = (L (n + 1)).delta t)
    (hqρ : ∀ n : ℕ, ∀ t ∈ Icc (0 : ℝ) (n : ℝ), q.neckRadius t = (L (n + 1)).neckRadius t) :
    AntitoneOn q.delta (Ici 0) ∧ AntitoneOn q.neckRadius (Ici 0) ∧
      Tendsto q.delta atTop (nhds 0) ∧ AccuracyDecaySupply_C11S q.delta ∧
      RadiusAntitoneSupply_C11S q := by
  obtain ⟨h1, h2, h3⟩ := accuracyDecay_of_chain_C11RA E hElt hEge L hpast hanti a hafter ha q hqδ
  have h4 := radiusAntitone_of_chain_C11RA E hElt hEge L hpast hradius q hqρ
  exact ⟨h1, h4, h2, h3, h4⟩

/-! ## Consumer：step 链 -/

/-- step 链的 ρ（`1/(t+1)`，与 `n` 无关）antitone。 -/
theorem stepChain_radius_antitone_C11RA (n : ℕ) :
    AntitoneOn (stepChain_C11RA n).neckRadius (Ici 0) := by
  intro s hs t _ hst
  simp only [mem_Ici] at hs
  change 1 / (t + 1) ≤ 1 / (s + 1)
  exact one_div_le_one_div_of_le (by positivity) (by linarith)

/-- **Consumer（G2）**：step 链的 diagonal 同时满足 S1 与 S2（`q :=` diagonal 本身）。 -/
theorem stepChain_S1_S2_C11RA :
    AccuracyDecaySupply_C11S (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)).delta ∧
      RadiusAntitoneSupply_C11S (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1)) := by
  have hcompat := fun (m n : ℕ) (hmn : m ≤ n) (t : ℝ) (ht : t ∈ Icc (0 : ℝ) (m : ℝ)) =>
    chain_diagonal_compat_C11RA (fun n => (n : ℝ)) (fun n => by simp) (fun n => by simp)
      stepChain_C11RA stepChain_past_C11RA m n hmn t ht
  have h := chain_S1_S2_C11RA (fun n => (n : ℝ)) (fun n => by simp) (fun n => by simp)
    stepChain_C11RA stepChain_past_C11RA stepChain_antitone_C11RA
    stepChain_radius_antitone_C11RA (fun n => 1 / ((n : ℝ) + 3))
    (fun n t ht => stepChain_after_C11RA n t ht)
    (fun n => one_div_le_one_div_of_le (by positivity) (by linarith))
    (CutoffParameters.diagonal fun n => stepChain_C11RA (n + 1))
    (fun n t ht => (CutoffParameters.diagonal_eq_on_prefix _ hcompat n ht).1)
    (fun n t ht => (CutoffParameters.diagonal_eq_on_prefix _ hcompat n ht).2.1)
  exact ⟨h.2.2.2.1, h.2.2.2.2⟩

end GC.LongTime.Ch11
