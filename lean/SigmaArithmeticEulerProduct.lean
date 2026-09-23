import SigmaOpSpectral
import Mathlib.NumberTheory.EulerProduct.DirichletLSeries

/-! The numerical prime-product clause of `final:B4`.  This reuses Mathlib's
native convergent Euler product.  It asserts neither an operator trace nor the
inverse theorem for arbitrary real generator multisets. -/

namespace Sigma
noncomputable section

/-- The numerical Dirichlet series and the actual convergent prime product have
the same value throughout the complex half-plane in the paper. -/
theorem numerical_zeta_series_euler_product {s : ℂ} (hs : 1 < s.re) :
    HasSum (fun n : ℕ => 1 / (n + 1 : ℂ) ^ s) (riemannZeta s) ∧
      HasProd (fun p : Nat.Primes => (1 - (p : ℂ) ^ (-s))⁻¹) (riemannZeta s) :=
  ⟨operator_zeta_eigenvalue_hasSum hs, riemannZeta_eulerProduct_hasProd hs⟩

theorem numerical_zeta_euler_product_identity {s : ℂ} (hs : 1 < s.re) :
    (∑' n : ℕ, 1 / (n + 1 : ℂ) ^ s) =
      ∏' p : Nat.Primes, (1 - (p : ℂ) ^ (-s))⁻¹ := by
  rw [(numerical_zeta_series_euler_product hs).1.tsum_eq,
    (numerical_zeta_series_euler_product hs).2.tprod_eq]

end
end Sigma
