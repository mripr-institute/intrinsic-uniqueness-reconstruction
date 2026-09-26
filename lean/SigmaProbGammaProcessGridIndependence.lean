import SigmaProbGammaProcessGrid

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- Adjacent increments of an arbitrary ordered finite collection of dyadic
observation times are independent, even when the times lie on different levels
or repeat. -/
theorem gamma_dyadic_process_grid_independent (n : ℕ) (a : ℕ → ℕ × ℕ)
    (ha : Monotone (fun k => gammaDyadicTime (a k))) :
    iIndepFun (fun _ : Fin n => inferInstance)
      (fun i : Fin n => fun ω => gammaDyadicProcessGrid (a (i.val+1)) ω-
        gammaDyadicProcessGrid (a i.val) ω) poissonClockProbability := by
  classical
  let N := (Finset.range (n+1)).sup (fun k => (a k).1)
  have hN (k : ℕ) (hk : k ≤ n) : (a k).1 ≤ N :=
    Finset.le_sup (f := fun k => (a k).1) (Finset.mem_range.mpr (by omega))
  let b : ℕ → ℕ := fun k => gammaDyadicRescale N (a k)
  have hb {j k : ℕ} (hjk : j ≤ k) (hk : k ≤ n) : b j ≤ b k :=
    gamma_dyadic_rescale_mono N (a j) (a k) (hN j (hjk.trans hk)) (hN k hk) (ha hjk)
  let s : Fin n → Finset ℕ := fun i => Finset.Ico (b i.val) (b (i.val+1))
  have hdis : Pairwise (fun i j => Disjoint (s i) (s j)) := by
    intro i j hij
    apply Finset.disjoint_left.mpr
    intro k hki hkj
    have hi := Finset.mem_Ico.mp hki
    have hj := Finset.mem_Ico.mp hkj
    have hijv : i.val ≠ j.val := fun h => hij (Fin.ext h)
    rcases lt_or_gt_of_ne hijv with hij' | hji'
    · have hh := hb (show i.val+1 ≤ j.val by omega) (Nat.le_of_lt j.isLt)
      omega
    · have hh := hb (show j.val+1 ≤ i.val by omega) (Nat.le_of_lt i.isLt)
      omega
  have hg := gamma_process_independent_finite_groups poissonClockProbability
    (gammaDyadicIncrement gammaDyadicRaw N)
    (gamma_dyadic_increment_measurable _ (gamma_dyadic_inputs_measurable _) N)
    (gamma_dyadic_process_increments_independent N) s hdis
    (fun i z => ∑ k : s i, z k)
    (fun i => Finset.measurable_sum _ (fun k hk => measurable_pi_apply k))
  have he (i : Fin n) (ω : PoissonClockSpace) :
      (∑ k : s i, gammaDyadicIncrement gammaDyadicRaw N k ω) =
        gammaDyadicProcessGrid (a (i.val+1)) ω-gammaDyadicProcessGrid (a i.val) ω := by
    rw [Finset.sum_coe_sort (s i) (fun k => gammaDyadicIncrement gammaDyadicRaw N k ω)]
    rw [← gamma_dyadic_rescale_grid N (a (i.val+1)) (hN _ (by omega)),
      ← gamma_dyadic_rescale_grid N (a i.val) (hN _ (Nat.le_of_lt i.isLt))]
    exact (gamma_dyadic_grid_sub N (b i.val) (b (i.val+1))
      (hb (Nat.le_succ _) (by omega)) ω).symm
  simpa only [he] using hg

end
end Sigma
