import Mathlib

/-- A positive integer is powerful when every prime divisor occurs to exponent at least two. -/
def Powerful (n : ℕ) : Prop :=
  ∀ p : ℕ, Nat.Prime p → p ∣ n → p ^ 2 ∣ n

lemma powerful_prime_cube (p : ℕ) (hp : Nat.Prime p) : Powerful (p ^ 3) := by
  intro q hq hqdiv
  rcases (Nat.dvd_prime_pow hp).mp hqdiv with ⟨k, hk, rfl⟩
  have hk0 : k ≠ 0 := by
    intro hkzero
    subst k
    exact hq.ne_one rfl
  have hkc : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  rcases hkc with rfl | rfl | rfl
  · simpa using (pow_dvd_pow p (by omega : 2 ≤ 3))
  · exact False.elim ((Nat.Prime.not_prime_pow (by omega)) hq)
  · exact False.elim ((Nat.Prime.not_prime_pow (by omega)) hq)

lemma powerful_12168 : Powerful (2 ^ 3 * 3 ^ 2 * 13 ^ 2) := by
  intro p hp hdiv
  rcases (hp.dvd_mul).mp hdiv with hleft | h13
  · rcases (hp.dvd_mul).mp hleft with h2 | h3
    · rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 2)).mp h2 with ⟨k, hk, rfl⟩
      have hk0 : k ≠ 0 := by
        intro hkzero
        subst k
        exact hp.ne_one rfl
      have hkc : k = 1 ∨ k = 2 ∨ k = 3 := by omega
      rcases hkc with rfl | rfl | rfl
      · norm_num
      · exact False.elim ((Nat.Prime.not_prime_pow (by omega)) hp)
      · exact False.elim ((Nat.Prime.not_prime_pow (by omega)) hp)
    · rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp h3 with ⟨k, hk, rfl⟩
      have hk0 : k ≠ 0 := by
        intro hkzero
        subst k
        exact hp.ne_one rfl
      have hkc : k = 1 ∨ k = 2 := by omega
      rcases hkc with rfl | rfl
      · norm_num
      · exact False.elim ((Nat.Prime.not_prime_pow (by omega)) hp)
  · rcases (Nat.dvd_prime_pow (by norm_num : Nat.Prime 13)).mp h13 with ⟨k, hk, rfl⟩
    have hk0 : k ≠ 0 := by
      intro hkzero
      subst k
      exact hp.ne_one rfl
    have hkc : k = 1 ∨ k = 2 := by omega
    rcases hkc with rfl | rfl
    · norm_num
    · exact False.elim ((Nat.Prime.not_prime_pow (by omega)) hp)

lemma not_square_12167 : ¬ ∃ k : ℕ, 12167 = k ^ 2 := by
  rintro ⟨k, hk⟩
  have hkmod := congrArg (fun x : ℕ => x % 3) hk
  have hres : k % 3 = 0 ∨ k % 3 = 1 ∨ k % 3 = 2 := by omega
  rcases hres with h0 | h1 | h2
  · norm_num [pow_two, Nat.mul_mod, h0] at hkmod
  · norm_num [pow_two, Nat.mul_mod, h1] at hkmod
  · norm_num [pow_two, Nat.mul_mod, h2] at hkmod

lemma not_square_12168 : ¬ ∃ k : ℕ, 12168 = k ^ 2 := by
  rintro ⟨k, hk⟩
  have hkmod := congrArg (fun x : ℕ => x % 5) hk
  have hres : k % 5 = 0 ∨ k % 5 = 1 ∨ k % 5 = 2 ∨ k % 5 = 3 ∨ k % 5 = 4 := by omega
  rcases hres with h0 | h1 | h2 | h3 | h4
  · norm_num [pow_two, Nat.mul_mod, h0] at hkmod
  · norm_num [pow_two, Nat.mul_mod, h1] at hkmod
  · norm_num [pow_two, Nat.mul_mod, h2] at hkmod
  · norm_num [pow_two, Nat.mul_mod, h3] at hkmod
  · norm_num [pow_two, Nat.mul_mod, h4] at hkmod

/-- Golomb's counterexample to the claim that one of two consecutive powerful
    positive integers must be a square. -/
theorem jsp_000301_counterexample :
    ∃ n : ℕ,
      Powerful n ∧ Powerful (n + 1) ∧
      (¬ ∃ k : ℕ, n = k ^ 2) ∧
      (¬ ∃ k : ℕ, n + 1 = k ^ 2) := by
  refine ⟨12167, ?_, ?_, not_square_12167, ?_⟩
  · convert powerful_prime_cube 23 (by norm_num : Nat.Prime 23) using 1
  · norm_num [show (12168 : ℕ) = 2 ^ 3 * 3 ^ 2 * 13 ^ 2 by norm_num]
    exact powerful_12168
  · norm_num
    intro k hk
    exact not_square_12168 ⟨k, hk⟩
