import SigmaOpDeterminantMultiplicity

namespace Sigma
noncomputable section
open scoped Topology

theorem spectral_determinant_zero_multisets_recover {ι κ : Type*} (regularized : Bool)
    (c : ι → ℂ) (d : κ → ℂ)
    (hc : Summable (fun i => ‖c i‖^(determinantSummabilityPower regularized)))
    (hd : Summable (fun i => ‖d i‖^(determinantSummabilityPower regularized)))
    (hc0 : ∀ i, c i ≠ 0) (hd0 : ∀ i, d i ≠ 0)
    (hzeros : ∀ z : ℂ, (spectral_determinant_entire regularized c hc z).order =
      (spectral_determinant_entire regularized d hd z).order) :
    ∃ e : ι ≃ κ, ∀ i, d (e i) = c i := by
  classical
  have he (a : ℂ) : Nonempty ({i // c i = a} ≃ {j // d j = a}) := by
    by_cases ha : a = 0
    · subst a
      letI : IsEmpty {i // c i = 0} := ⟨fun i => hc0 i.val i.property⟩
      letI : IsEmpty {j // d j = 0} := ⟨fun j => hd0 j.val j.property⟩
      exact ⟨Equiv.equivOfIsEmpty _ _⟩
    · have heq (w : ℂ) : 1+(-a⁻¹)*w = 0 ↔ w = a := by
        constructor
        · intro h
          have hh := congrArg (fun x : ℂ => a*x) h
          field_simp at hh
          linear_combination -hh
        · intro h
          subst w
          simp [ha]
      have hcset : {i | 1+(-a⁻¹)*c i = 0} = {i | c i = a} := by ext i; exact heq _
      have hdset : {j | 1+(-a⁻¹)*d j = 0} = {j | d j = a} := by ext i; exact heq _
      have hcfinite := spectral_determinant_root_set_finite regularized c hc (-a⁻¹)
      have hdfinite := spectral_determinant_root_set_finite regularized d hd (-a⁻¹)
      rw [hcset] at hcfinite
      rw [hdset] at hdfinite
      letI : Finite {i // c i = a} := hcfinite.to_subtype
      letI : Finite {j // d j = a} := hdfinite.to_subtype
      letI := Fintype.ofFinite {i // c i = a}
      letI := Fintype.ofFinite {j // d j = a}
      have hh := hzeros (-a⁻¹)
      rw [spectral_determinant_zero_order regularized c hc,
        spectral_determinant_zero_order regularized d hd] at hh
      have hcard : Nat.card {i // c i = a} = Nat.card {j // d j = a} := by
        have hh' : Nat.card {i // 1+(-a⁻¹)*c i = 0} = Nat.card {j // 1+(-a⁻¹)*d j = 0} :=
          WithTop.coe_inj.mp hh
        simpa only [heq] using hh'
      exact ⟨Fintype.equivOfCardEq (by simpa only [Nat.card_eq_fintype_card] using hcard)⟩
  let e := Equiv.ofFiberEquiv (fun a => (he a).some)
  exact ⟨e, Equiv.ofFiberEquiv_map _⟩

end
end Sigma
