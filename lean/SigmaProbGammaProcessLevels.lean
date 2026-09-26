import SigmaProbGammaProcessRefinement
import SigmaProbGammaProcessPrefix
import SigmaProbGammaProcessFiltration

namespace Sigma
noncomputable section
open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal BigOperators

/-- The vector splitting map is exactly the recursive dyadic refinement. -/
theorem gamma_dyadic_flatten_children {Ω : Type*} (raw : (ℕ × ℕ) → Ω → ℝ)
    (n K : ℕ) (ω : Ω) (j : Fin (K*2)) :
    gammaProcessPairFlatten K
      (fun k : Fin K => (gammaDyadicIncrement raw n k ω * raw (n+1,k) ω,
        gammaDyadicIncrement raw n k ω * (1-raw (n+1,k) ω))) j =
      gammaDyadicIncrement raw (n+1) j ω := by
  obtain ⟨⟨k,i⟩,rfl⟩ := finProdFinEquiv.surjective j
  simp only [gammaProcessPairFlatten, Equiv.symm_apply_apply]
  fin_cases i
  · simpa [finProdFinEquiv, Nat.mul_comm] using
      (gamma_dyadic_increment_even raw n k ω).symm
  · simpa [finProdFinEquiv, Nat.mul_comm, Nat.add_comm] using
      (gamma_dyadic_increment_odd raw n k ω).symm

/-- Every finite prefix at every dyadic level has the literal independent
Gamma product law. The only analytic input is the one-parent Gamma–Beta law. -/
theorem gamma_dyadic_level_product_law (beta : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (beta n)]
    (hsplit : ∀ n, ((gammaCompletion (gammaDyadicDuration n)).prod (beta n)).map
      (fun p : ℝ × ℝ => (p.1*p.2,p.1*(1-p.2))) =
      (gammaCompletion (gammaDyadicDuration n/2)).prod
        (gammaCompletion (gammaDyadicDuration n/2))) (n K : ℕ) :
    poissonClockProbability.map (fun ω (k : Fin K) =>
      gammaDyadicIncrement (gammaDyadicInputs beta) n k ω) =
      Measure.pi (fun _ : Fin K => gammaCompletion (gammaDyadicDuration n)) := by
  let raw := gammaDyadicInputs beta
  have hm := gamma_dyadic_inputs_measurable beta
  have hi := gamma_dyadic_inputs_independent beta
  induction n generalizing K with
  | zero =>
    let e : Fin K ↪ ℕ × ℕ := ⟨fun k => (0,k), fun i j h => Fin.ext (congrArg Prod.snd h)⟩
    have hh := gamma_process_finite_joint_law poissonClockProbability
      (fun k : Fin K => raw (0,k)) (fun k => hm (0,k))
      (gamma_process_independent_reindex _ _ hi e)
    simpa [raw, gammaDyadicIncrement, gamma_dyadic_inputs_law, gammaDyadicInputLaw,
      gammaDyadicDuration] using hh
  | succ n ih =>
    have hinc := gamma_dyadic_increment_measurable raw hm n
    have hin := gamma_process_prefix_independent poissonClockProbability
      (gammaDyadicIncrement raw n) hinc (gammaDyadicDuration n) ih
    have hlaw := gamma_process_prefix_marginal poissonClockProbability
      (gammaDyadicIncrement raw n) hinc (gammaDyadicDuration n) ih
    let e : Fin K ↪ ℕ := ⟨Fin.val, Fin.val_injective⟩
    let b : Fin K ↪ ℕ × ℕ := ⟨fun k => (n+1,k), fun i j h => Fin.ext (congrArg Prod.snd h)⟩
    have hp := gamma_process_paired_vector_law poissonClockProbability
      (fun k : Fin K => gammaDyadicIncrement raw n k) (fun k : Fin K => raw (n+1,k))
      (fun k => hinc k) (fun k => hm (n+1,k))
      (gamma_process_independent_reindex _ _ hin e)
      (gamma_process_independent_reindex _ _ hi b)
      (gamma_dyadic_parent_split_vectors_independent _ raw hm hi n K)
    simp only [hlaw, raw, gamma_dyadic_inputs_law, gammaDyadicInputLaw] at hp
    have hs := gamma_process_split_product_law K (gammaDyadicDuration n) (beta n) (hsplit n)
    rw [← hp] at hs
    have hsm : Measurable (fun z : Fin K → ℝ×ℝ => gammaProcessPairFlatten K
      (fun k => ((z k).1*(z k).2,(z k).1*(1-(z k).2)))) := by
      apply (gamma_process_pair_flatten_measurable K).comp
      fun_prop
    rw [Measure.map_map hsm
      (measurable_pi_lambda _ (fun k : Fin K => (hinc k).prod_mk (hm (n+1,k))))] at hs
    have he : (fun ω => (fun z : Fin K → ℝ×ℝ => gammaProcessPairFlatten K
        (fun k => ((z k).1*(z k).2,(z k).1*(1-(z k).2))))
        (fun k => (gammaDyadicIncrement raw n k ω,raw (n+1,k) ω))) =
        (fun ω (j : Fin (K*2)) => gammaDyadicIncrement raw (n+1) j ω) := by
      funext ω j
      exact gamma_dyadic_flatten_children raw n K ω j
    change poissonClockProbability.map (fun ω => (fun z : Fin K → ℝ×ℝ => gammaProcessPairFlatten K
        (fun k => ((z k).1*(z k).2,(z k).1*(1-(z k).2))))
        (fun k => (gammaDyadicIncrement raw n k ω,raw (n+1,k) ω))) = _ at hs
    rw [he, ← gamma_dyadic_duration_succ] at hs
    let eK : Fin K ↪ Fin (K*2) := ⟨fun k => ⟨k, by have hk := k.isLt; omega⟩,
      fun i j h => Fin.ext (congrArg (fun x : Fin (K*2) => x.val) h)⟩
    exact gamma_process_prefix_restrict poissonClockProbability
      (fun k : Fin (K*2) => gammaDyadicIncrement raw (n+1) k)
      (fun k => gamma_dyadic_increment_measurable raw hm (n+1) k)
      (gammaDyadicDuration (n+1)) hs eK

theorem gamma_dyadic_level_independent (beta : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (beta n)]
    (hsplit : ∀ n, ((gammaCompletion (gammaDyadicDuration n)).prod (beta n)).map
      (fun p : ℝ × ℝ => (p.1*p.2,p.1*(1-p.2))) =
      (gammaCompletion (gammaDyadicDuration n/2)).prod
        (gammaCompletion (gammaDyadicDuration n/2))) (n : ℕ) :
    iIndepFun (fun _ => inferInstance)
      (gammaDyadicIncrement (gammaDyadicInputs beta) n) poissonClockProbability :=
  gamma_process_prefix_independent _ _
    (gamma_dyadic_increment_measurable _ (gamma_dyadic_inputs_measurable beta) n)
    _ (gamma_dyadic_level_product_law beta hsplit n)

theorem gamma_dyadic_increment_law (beta : ℕ → Measure ℝ)
    [∀ n, IsProbabilityMeasure (beta n)]
    (hsplit : ∀ n, ((gammaCompletion (gammaDyadicDuration n)).prod (beta n)).map
      (fun p : ℝ × ℝ => (p.1*p.2,p.1*(1-p.2))) =
      (gammaCompletion (gammaDyadicDuration n/2)).prod
        (gammaCompletion (gammaDyadicDuration n/2))) (n k : ℕ) :
    poissonClockProbability.map (gammaDyadicIncrement (gammaDyadicInputs beta) n k) =
      gammaCompletion (gammaDyadicDuration n) :=
  gamma_process_prefix_marginal _ _
    (gamma_dyadic_increment_measurable _ (gamma_dyadic_inputs_measurable beta) n)
    _ (gamma_dyadic_level_product_law beta hsplit n) k

end
end Sigma
