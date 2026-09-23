import SigmaArithmeticEulerProduct
import Mathlib.Data.Set.Finite.Lemmas

/-! Consequences of actual positive Euler-product convergence.  The generator
set is not assumed countable or locally finite. -/

namespace Sigma
noncomputable section
open Set Filter
open scoped Topology BigOperators

def realEulerFactor (q : ℝ) (m : ℕ) (s : ℝ) : ℝ :=
  ((1 - q ^ (-s)) ^ m)⁻¹

theorem real_euler_factor_pos {q s : ℝ} (hq : 1 < q) (hs : 0 < s) (m : ℕ) :
    0 < realEulerFactor q m s := by
  exact inv_pos.mpr (pow_pos (sub_pos.mpr
    (Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs))) m)

theorem real_euler_log_factor (q s : ℝ) (m : ℕ) :
    Real.log (realEulerFactor q m s) = (m : ℝ) * (-Real.log (1 - q ^ (-s))) := by
  rw [realEulerFactor, Real.log_inv, Real.log_pow]
  ring

theorem real_euler_log_factor_lower {q s : ℝ} (hq : 1 < q) (hs : 0 < s)
    {m : ℕ} (hm : 0 < m) :
    q ^ (-s) ≤ Real.log (realEulerFactor q m s) := by
  have hp := Real.rpow_pos_of_pos (lt_trans zero_lt_one hq) (-s)
  have hlt := Real.rpow_lt_one_of_one_lt_of_neg hq (neg_neg_of_pos hs)
  have hl := Real.log_le_sub_one_of_pos (sub_pos.mpr hlt)
  have hb : q ^ (-s) ≤ -Real.log (1 - q ^ (-s)) := by linarith
  rw [real_euler_log_factor]
  have hm' : (1 : ℝ) ≤ m := by exact_mod_cast hm
  nlinarith

theorem real_euler_product_log_hasSum {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z) :
    HasSum (fun q : Q => Real.log (realEulerFactor q (m q) s)) (Real.log Z) := by
  have h := (Real.continuousAt_log hZ.ne').tendsto.comp hprod
  change Tendsto (fun F : Finset Q => ∑ q ∈ F, Real.log (realEulerFactor q (m q) s)) atTop (𝓝 (Real.log Z))
  convert h using 1
  funext F
  exact (Real.log_prod F _ (fun q _ => (real_euler_factor_pos (hQ q q.property) hs (m q)).ne')).symm

theorem real_euler_generators_bounded_finite {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z)
    (M : ℝ) : (Q ∩ Iic M).Finite := by
  by_cases hM : 1 < M
  · have hsum := (real_euler_product_log_hasSum hQ hs hZ hprod).summable
    let f : ↑(Q ∩ Iic M) → Q := fun q => ⟨q, q.property.1⟩
    have hf : Function.Injective f := by
      intro a b h
      apply Subtype.ext
      exact congrArg (fun q : Q => (q : ℝ)) h
    have hsub := hsum.comp_injective hf
    have hc : Summable (fun _ : ↑(Q ∩ Iic M) => M ^ (-s)) := by
      apply Summable.of_nonneg_of_le (fun _ => (Real.rpow_pos_of_pos (by linarith) _).le) _ hsub
      intro q
      exact (Real.rpow_le_rpow_of_nonpos (by linarith [hQ q q.property.1])
        q.property.2 (by linarith)).trans
        (real_euler_log_factor_lower (hQ q q.property.1) hs (hm (f q)))
    haveI : Finite ↑(Q ∩ Iic M) := Finite.of_summable_const
      (Real.rpow_pos_of_pos (by linarith) _) hc
    exact Set.toFinite _
  · have he : Q ∩ Iic M = ∅ := by
      apply Set.eq_empty_iff_forall_not_mem.mpr
      intro q hq
      have := hQ q hq.1
      have := hq.2
      simp only [mem_Iic] at *
      linarith
    rw [he]
    exact finite_empty

theorem real_euler_generators_countable {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z) : Q.Countable := by
  have hc : (⋃ n : ℕ, Q ∩ Iic (n : ℝ)).Countable :=
    Set.countable_iUnion fun n =>
      (real_euler_generators_bounded_finite hQ hm hs hZ hprod n).countable
  apply hc.mono
  intro q hq
  obtain ⟨n, hn⟩ := exists_nat_gt q
  exact Set.mem_iUnion.mpr ⟨n, hq, hn.le⟩

theorem real_euler_generators_least {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z)
    (hne : Q.Nonempty) : ∃ q, IsLeast Q q ∧ 1 < q := by
  obtain ⟨a, ha⟩ := hne
  obtain ⟨q, hq, hmin⟩ := Set.exists_min_image (Q ∩ Iic a) (fun x : ℝ => x)
    (real_euler_generators_bounded_finite hQ hm hs hZ hprod a) ⟨a, ha, le_refl a⟩
  refine ⟨q, ⟨hq.1, ?_⟩, hQ q hq.1⟩
  intro b hb
  by_cases hba : b ≤ a
  · exact hmin b ⟨hb, hba⟩
  · exact hq.2.trans (le_of_not_ge hba)

theorem real_euler_product_gt_one {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z)
    (hne : Q.Nonempty) : 1 < Z := by
  have hsum := real_euler_product_log_hasSum hQ hs hZ hprod
  obtain ⟨q, hq⟩ := hne
  have hle := le_hasSum hsum ⟨q, hq⟩ (fun r _ =>
    (Real.rpow_pos_of_pos (by linarith [hQ r r.property]) (-s)).le.trans
      (real_euler_log_factor_lower (hQ r r.property) hs (hm r)))
  apply (Real.log_pos_iff hZ).mp
  exact (Real.rpow_pos_of_pos (by linarith [hQ q hq]) (-s)).trans_le
    ((real_euler_log_factor_lower (hQ q hq) hs (hm ⟨q, hq⟩)).trans hle)

theorem real_euler_product_eq_one_iff_empty {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hm : ∀ q, 0 < m q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z) :
    Z = 1 ↔ Q = ∅ := by
  constructor
  · intro h
    by_contra hn
    have := real_euler_product_gt_one hQ hm hs hZ hprod (Set.nonempty_iff_ne_empty.mpr hn)
    linarith
  · intro h
    subst Q
    haveI : IsEmpty (↥(∅ : Set ℝ)) := inferInstance
    have hf : (fun q : (↥(∅ : Set ℝ)) => realEulerFactor q (m q) s) = fun _ => 1 := by
      funext q
      exact isEmptyElim q
    rw [hf] at hprod
    exact hprod.unique hasProd_one

/-- Removing a generator removes its entire multiplicity factor.  Convergence
of the residual product is derived, even if powers of distinct generators coincide. -/
theorem real_euler_product_remove_generator {Q : Set ℝ} {m : Q → ℕ} {s Z : ℝ}
    (hQ : ∀ q ∈ Q, 1 < q) (hs : 0 < s) (hZ : 0 < Z)
    (hprod : HasProd (fun q : Q => realEulerFactor q (m q) s) Z) (a : Q) :
    HasProd (fun q : {q : Q // q ∉ ({a} : Finset Q)} => realEulerFactor q.val (m q.val) s)
      (Z / realEulerFactor a (m a) s) ∧ 0 < Z / realEulerFactor a (m a) s := by
  classical
  have hsum := real_euler_product_log_hasSum hQ hs hZ hprod
  have hrest := (Finset.hasSum_iff_compl ({a} : Finset Q)).mp hsum
  simp only [Finset.sum_singleton] at hrest
  have he := hrest.rexp
  simp only [Function.comp_apply, Real.exp_sub,
    Real.exp_log hZ, Real.exp_log (real_euler_factor_pos (hQ a a.property) hs (m a))] at he
  have hexp : (fun q : {q : Q // q ∉ ({a} : Finset Q)} => Real.exp (Real.log (realEulerFactor q.val (m q.val) s))) =
      (fun q : {q : Q // q ∉ ({a} : Finset Q)} => realEulerFactor q.val (m q.val) s) := by
    funext q
    exact Real.exp_log (real_euler_factor_pos (hQ q.val q.val.property) hs (m q.val))
  change HasProd (fun q : {q : Q // q ∉ ({a} : Finset Q)} => Real.exp (Real.log (realEulerFactor q.val (m q.val) s)))
    (Z / realEulerFactor a (m a) s) at he
  rw [hexp] at he
  exact ⟨he, div_pos hZ (real_euler_factor_pos (hQ a a.property) hs (m a))⟩

end
end Sigma
